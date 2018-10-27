module TTImp.Elab.Unelab

import TTImp.TTImp
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

mutual
  -- Turn a term back into an unannotated TTImp. Returns the type of the
  -- unelaborated term so that we can work out where to put the implicit 
  -- applications
  unelabTy : {auto c : Ref Ctxt Defs} ->
           annot -> Env Term vars -> Term vars -> 
           Core annot (RawImp annot, Term vars)
  unelabTy loc env (Local {x} _ el) 
      = pure (IVar loc x, binderType (getBinder el env))
  unelabTy loc env (Ref nt n)
      = do defs <- get Ctxt
           case lookupDefTyExact n (gamma defs) of
                Nothing => pure (IHole loc (nameRoot n),
                                 Erased) -- should never happen on a well typed term!
                                    -- may happen in error messages where we haven't saved
                                    -- holes in the context
                Just (Hole _ False _, ty) => pure (IHole loc (nameRoot n), embed ty)
                Just (_, ty) => pure (IVar loc n, embed ty)
  unelabTy loc env (Bind x b sc)
      = do (sc', scty) <- unelabTy loc (b :: env) sc
           unelabBinder loc env x b sc sc' scty
  unelabTy loc env (App fn arg)
      = do (fn', fnty) <- unelabTy loc env fn
           case fn' of
               IHole _ _ => pure (fn', Erased)
               _ => do (arg', argty) <- unelabTy loc env arg
                       defs <- get Ctxt
                       case nf defs env fnty of
                            NBind x (Pi rig Explicit ty) sc
                              => pure (IApp loc fn' arg', 
                                       quote defs env (sc (toClosure defaultOpts env arg)))
                            NBind x (Pi rig p ty) sc
                              => pure (IImplicitApp loc fn' (Just x) arg', 
                                       quote defs env (sc (toClosure defaultOpts env arg)))
                            _ => pure (IApp loc fn' arg', Erased)
  unelabTy loc env (PrimVal c) = pure (IPrimVal loc c, Erased)
  unelabTy loc env Erased = pure (Implicit loc, Erased)
  unelabTy loc env TType = pure (IType loc, TType)
  unelabTy loc _ _ = pure (Implicit loc, Erased)

  unelabBinder : {auto c : Ref Ctxt Defs} ->
                 annot -> Env Term vars -> (x : Name) ->
                 Binder (Term vars) -> Term (x :: vars) ->
                 RawImp annot -> Term (x :: vars) -> 
                 Core annot (RawImp annot, Term vars)
  unelabBinder loc env x (Lam rig p ty) sctm sc scty
      = do (ty', _) <- unelabTy loc env ty
           pure (ILam loc rig p (Just x) ty' sc, Bind x (Pi rig p ty) scty)
  unelabBinder loc env x (Let rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy loc env val
           (ty', _) <- unelabTy loc env ty
           pure (ILet loc rig x ty' val' sc, Bind x (Let rig val ty) scty)
  unelabBinder loc env x (Pi rig p ty) sctm sc scty 
      = do (ty', _) <- unelabTy loc env ty
           let nm = if used Here sctm || rig /= RigW
                       then Just x else Nothing
           pure (IPi loc rig p nm ty' sc, TType)
  unelabBinder loc env x (PVar rig ty) sctm sc scty
      = do (ty', _) <- unelabTy loc env ty
           pure (sc, Bind x (PVTy rig ty) scty)
  unelabBinder loc env x (PLet rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy loc env val
           (ty', _) <- unelabTy loc env ty
           pure (ILet loc rig x ty' val' sc, Bind x (PLet rig val ty) scty)
  unelabBinder loc env x (PVTy rig ty) sctm sc scty
      = do (ty', _) <- unelabTy loc env ty
           pure (sc, TType)

export
unelab : {auto c : Ref Ctxt Defs} ->
         annot -> Env Term vars -> Term vars -> Core annot (RawImp annot)
unelab loc env tm
    = do tm' <- unelabTy loc env tm
         pure $ fst tm'
