module TTImp.Elab.Unelab

import TTImp.TTImp
import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT

import Data.List

%default covering

used : Elem x vars -> Term vars -> Bool
used el (Local _ v) = sameVar el v
used {vars} el (Bind x b sc) = usedBinder b || used (There el) sc
  where
    usedBinder : Binder (Term vars) -> Bool
    usedBinder (Let _ val ty) = used el val || used el ty
    usedBinder (PLet _ val ty) = used el val || used el ty
    usedBinder b = used el (binderType b)
used el (App f a) = used el f || used el a
used el _ = False

data IArg annot
   = Exp annot (RawImp annot)
   | Imp annot (Maybe Name) (RawImp annot)

data UnelabMode = Full | NoSugar | ImplicitHoles

Eq UnelabMode where
   Full == Full = True
   NoSugar == NoSugar = True
   ImplicitHoles == ImplicitHoles = True
   _ == _ = False

mutual
  unelabCase : {auto c : Ref Ctxt Defs} ->
               Name -> List (IArg annot) -> RawImp annot ->
               Core annot (RawImp annot)
  unelabCase n args orig
      = do defs <- get Ctxt
           let Just glob = lookupGlobalExact n (gamma defs)
                | Nothing => pure orig
           let PMDef _ pargs treect _ pats = definition glob
                | _ => pure orig
           let Just argpos = findArgPos treect
                | _ => pure orig
           if length args == length pargs
              then mkCase pats argpos 0 args
              else pure orig
    where
      pos : Elem v vs -> Nat
      pos Here = 0
      pos (There p) = S (pos p)

      -- Need to find the position of the scrutinee to rebuild original
      -- case correctly
      findArgPos : CaseTree as -> Maybe Nat
      findArgPos (Case el _ _) = Just (pos el)
      findArgPos _ = Nothing

      idxOrDefault : Nat -> a -> List a -> a
      idxOrDefault Z def (x :: xs) = x
      idxOrDefault (S k) def (_ :: xs) = idxOrDefault k def xs
      idxOrDefault _ def [] = def

      getNth : Nat -> Term vars -> Term vars
      getNth n tm with (unapply tm)
        getNth n (apply f args) | ArgsList = idxOrDefault n f args

      nthArg : Env Term vars -> Nat -> Term vars ->
                (vars' ** (Env Term vars', Term vars'))
      nthArg env drop (App f a) = (_ ** (env, getNth drop (App f a)))
      nthArg env drop (Bind x b sc) = nthArg (b :: env) drop sc
      nthArg env drop tm = (_ ** (env, Erased))

      dropEnv : List Name -> Env Term vars -> Term vars ->
                (vars' ** (Env Term vars', Term vars'))
      dropEnv (n :: ns) env (Bind x b sc) = dropEnv ns (b :: env) sc
      dropEnv ns env tm = (_ ** (env, tm))

      mkClause : annot -> Nat -> (List Name, ClosedTerm, ClosedTerm) ->
                 Core annot (ImpClause annot)
      mkClause loc dropped (vs, lhs, rhs)
          = do let (_ ** (env, pat)) = nthArg [] dropped lhs
               lhs' <- unelabTy Full loc env pat
               let (_ ** (env, rhs)) = dropEnv vs [] rhs
               rhs' <- unelabTy Full loc env rhs
               pure (PatClause loc (fst lhs') (fst rhs'))

      mkCase : List (List Name, ClosedTerm, ClosedTerm) ->
               Nat -> Nat -> List (IArg annot) -> Core annot (RawImp annot)
      mkCase pats (S k) dropped (_ :: args) = mkCase pats k (S dropped) args
      mkCase pats Z dropped (Exp loc tm :: _)
          = do pats' <- traverse (mkClause loc dropped) pats
               pure $ ICase loc tm (Implicit loc) pats'
      mkCase _ _ _ _ = pure orig

  getFnArgs : RawImp annot -> List (IArg annot) -> 
              (RawImp annot, List (IArg annot))
  getFnArgs (IApp loc f arg) args = getFnArgs f (Exp loc arg :: args)
  getFnArgs (IImplicitApp loc f n arg) args = getFnArgs f (Imp loc n arg :: args)
  getFnArgs tm args = (tm, args)

  unelabSugar : {auto c : Ref Ctxt Defs} ->
                (umode : UnelabMode) ->
                (RawImp annot, Term vars) ->
                Core annot (RawImp annot, Term vars)
  unelabSugar NoSugar res = pure res
  unelabSugar _ (tm, ty) 
      = let (f, args) = getFnArgs tm [] in
            case f of
             IVar loc (GN (CaseBlock n i))
                 => pure (!(unelabCase (GN (CaseBlock n i)) args tm), ty)
             _ => pure (tm, ty)

  -- Turn a term back into an unannotated TTImp. Returns the type of the
  -- unelaborated term so that we can work out where to put the implicit 
  -- applications
  unelabTy : {auto c : Ref Ctxt Defs} ->
             (umode : UnelabMode) ->
             annot -> Env Term vars -> Term vars -> 
             Core annot (RawImp annot, Term vars)
  unelabTy umode loc env tm 
      = unelabSugar umode !(unelabTy' umode loc env tm)

  unelabTy' : {auto c : Ref Ctxt Defs} ->
              (umode : UnelabMode) ->
              annot -> Env Term vars -> Term vars -> 
              Core annot (RawImp annot, Term vars)
  unelabTy' umode loc env (Local {x} _ el) 
      = pure (IVar loc x, binderType (getBinder el env))
  unelabTy' umode loc env (Ref nt n)
      = do defs <- get Ctxt
           case (umode, lookupDefTyExact n (gamma defs)) of
                (ImplicitHoles, Nothing) 
                     => pure (Implicit loc, Erased)
                (_, Nothing)
                     => pure (IHole loc (nameRoot n),
                              Erased) -- should never happen on a well typed term!
                                 -- may happen in error messages where we haven't saved
                                 -- holes in the context
                (_, Just (Hole _ False _, ty)) 
                     => pure (IHole loc (nameRoot n), embed ty)
                (_, Just (_, ty)) 
                     => pure (IVar loc n, embed ty)
  unelabTy' umode loc env (Bind x b sc)
      = do (sc', scty) <- unelabTy umode loc (b :: env) sc
           unelabBinder umode loc env x b sc sc' scty
  unelabTy' umode loc env (App fn arg)
      = do (fn', fnty) <- unelabTy umode loc env fn
           case fn' of
               IHole _ _ => pure (fn', Erased)
               _ => do (arg', argty) <- unelabTy umode loc env arg
                       defs <- get Ctxt
                       case nf defs env fnty of
                            NBind x (Pi rig Explicit ty) sc
                              => pure (IApp loc fn' arg', 
                                       quote defs env (sc (toClosure defaultOpts env arg)))
                            NBind x (Pi rig p ty) sc
                              => pure (IImplicitApp loc fn' (Just x) arg', 
                                       quote defs env (sc (toClosure defaultOpts env arg)))
                            _ => pure (IApp loc fn' arg', Erased)
  unelabTy' umode loc env (PrimVal c) = pure (IPrimVal loc c, Erased)
  unelabTy' umode loc env Erased = pure (Implicit loc, Erased)
  unelabTy' umode loc env TType = pure (IType loc, TType)
  unelabTy' umode loc _ _ = pure (Implicit loc, Erased)

  unelabBinder : {auto c : Ref Ctxt Defs} ->
                 (umode : UnelabMode) ->
                 annot -> Env Term vars -> (x : Name) ->
                 Binder (Term vars) -> Term (x :: vars) ->
                 RawImp annot -> Term (x :: vars) -> 
                 Core annot (RawImp annot, Term vars)
  unelabBinder umode loc env x (Lam rig p ty) sctm sc scty
      = do (ty', _) <- unelabTy umode loc env ty
           pure (ILam loc rig p (Just x) ty' sc, Bind x (Pi rig p ty) scty)
  unelabBinder umode loc env x (Let rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy umode loc env val
           (ty', _) <- unelabTy umode loc env ty
           pure (ILet loc rig x ty' val' sc, Bind x (Let rig val ty) scty)
  unelabBinder umode loc env x (Pi rig p ty) sctm sc scty 
      = do (ty', _) <- unelabTy umode loc env ty
           let nm = if used Here sctm || rig /= RigW
                       then Just x else Nothing
           pure (IPi loc rig p nm ty' sc, TType)
  unelabBinder umode loc env x (PVar rig ty) sctm sc scty
      = do (ty', _) <- unelabTy umode loc env ty
           pure (sc, Bind x (PVTy rig ty) scty)
  unelabBinder umode loc env x (PLet rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy umode loc env val
           (ty', _) <- unelabTy umode loc env ty
           pure (ILet loc rig x ty' val' sc, Bind x (PLet rig val ty) scty)
  unelabBinder umode loc env x (PVTy rig ty) sctm sc scty
      = do (ty', _) <- unelabTy umode loc env ty
           pure (sc, TType)

export
unelabNoSugar : {auto c : Ref Ctxt Defs} ->
         annot -> Env Term vars -> Term vars -> Core annot (RawImp annot)
unelabNoSugar loc env tm
    = do tm' <- unelabTy NoSugar loc env tm
         pure $ fst tm'

export
unelabNoPatvars : {auto c : Ref Ctxt Defs} ->
         annot -> Env Term vars -> Term vars -> Core annot (RawImp annot)
unelabNoPatvars loc env tm
    = do tm' <- unelabTy ImplicitHoles loc env tm
         pure $ fst tm'

export
unelab : {auto c : Ref Ctxt Defs} ->
         annot -> Env Term vars -> Term vars -> Core annot (RawImp annot)
unelab loc env tm
    = do tm' <- unelabTy Full loc env tm
         pure $ fst tm'
