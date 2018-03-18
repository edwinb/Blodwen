module TTImp.Elab.Term

import TTImp.TTImp
import Core.Context
import Core.Normalise
import Core.TT

import Data.List

%default covering

used : Elem x vars -> Term vars -> Bool
used el (Local v) = sameVar el v
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
           Env Term vars -> Term vars -> Core annot (RawImp (), Term vars)
  unelabTy env (Local {x} el) 
      = pure (IVar () x, binderType (getBinder el env))
  unelabTy env (Ref nt n)
      = do defs <- get Ctxt
           case lookupTyExact n (gamma defs) of
                Nothing => pure (IVar () (UN ("BADNAME[" ++ show n ++"]")), 
                                 Erased) -- should never happen!
                Just ty => pure (IVar () n, embed ty)
  unelabTy env (Bind x b sc)
      = do (sc', scty) <- unelabTy (b :: env) sc
           unelabBinder env x b sc sc' scty
  unelabTy env (App fn arg)
      = do (fn', fnty) <- unelabTy env fn
           (arg', argty) <- unelabTy env arg
           defs <- get Ctxt
           case nf defs env fnty of
                NBind x (Pi rig Explicit ty) sc
                  => pure (IApp () fn' arg', 
                           quote defs env (sc (toClosure False env arg)))
                NBind x (Pi rig p ty) sc
                  => pure (IImplicitApp () fn' x arg', 
                           quote defs env (sc (toClosure False env arg)))
                _ => pure (IApp () fn' arg', Erased)
  unelabTy env (PrimVal c) = pure (IPrimVal () c, Erased)
  unelabTy env Erased = pure (Implicit (), Erased)
  unelabTy env TType = pure (IType (), TType)
  unelabTy _ _ = pure (Implicit (), Erased)

  unelabBinder : {auto c : Ref Ctxt Defs} ->
                 Env Term vars -> (x : Name) ->
                 Binder (Term vars) -> Term (x :: vars) ->
                 RawImp () -> Term (x :: vars) -> 
                 Core annot (RawImp (), Term vars)
  unelabBinder env x (Lam rig p ty) sctm sc scty
      = do (ty', _) <- unelabTy env ty
           pure (ILam () rig p x ty' sc, Bind x (Pi rig p ty) scty)
  unelabBinder env x (Let rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy env val
           (ty', _) <- unelabTy env ty
           pure (ILet () rig x ty' val' sc, Bind x (Let rig val ty) scty)
  unelabBinder env x (Pi rig p ty) sctm sc scty 
      = do (ty', _) <- unelabTy env ty
           let nm = if used Here sctm then Just x else Nothing
           pure (IPi () rig p nm ty' sc, TType)
  unelabBinder env x (PVar rig ty) sctm sc scty
      = do (ty', _) <- unelabTy env ty
           pure (sc, Bind x (PVTy rig ty) scty)
  unelabBinder env x (PLet rig val ty) sctm sc scty
      = do (val', vty) <- unelabTy env val
           (ty', _) <- unelabTy env ty
           pure (ILet () rig x ty' val' sc, Bind x (PLet rig val ty) scty)
  unelabBinder env x (PVTy rig ty) sctm sc scty
      = do (ty', _) <- unelabTy env ty
           pure (sc, TType)

export
unelab : {auto c : Ref Ctxt Defs} ->
         Env Term vars -> Term vars -> Core annot (RawImp ())
unelab env tm = pure $ fst !(unelabTy env tm)
