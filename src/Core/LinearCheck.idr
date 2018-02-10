module Core.LinearCheck

import Core.Context
import Core.Normalise
import Core.TT

import Data.List

%default covering

lookup : Elem x vars -> Env Term vars -> (RigCount, Term vars)
lookup Here (b :: bs) = (multiplicity b, weaken (binderType b))
lookup (There p) (b :: bs) 
    = case lookup p bs of
           (c, ty) => (c, weaken ty)

-- List of variable usages - we'll count the contents of specific variables
-- when discharging binders, to ensure that linear names are only used once
data Usage : List Name -> Type where
     Nil : Usage vars
     (::) : Elem x vars -> Usage vars -> Usage vars

Weaken Usage where
  weaken [] = []
  weaken (x :: xs) = There x :: weaken xs

doneScope : Usage (n :: vars) -> Usage vars
doneScope [] = []
doneScope (Here :: xs) = doneScope xs
doneScope (There p :: xs) = p :: doneScope xs

(++) : Usage ns -> Usage ns -> Usage ns
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

count : Elem x ns -> Usage ns -> Nat
count p [] = 0
count p (q :: xs) = if sameVar p q then 1 + count p xs else count p xs

-- Linearity checking of an already checked term. This serves two purposes:
--  + Checking correct usage of linear bindings
--  + updating hole types to reflect usage counts correctly
mutual
  lcheck : {auto c : Ref Ctxt Defs} ->
           annot -> RigCount -> Env Term vars -> Term vars -> 
           Core annot (Term vars, Term vars, Usage vars)
  lcheck {vars} loc rig env (Local {x} v) 
      = let (rigb, ty) = lookup v env in
            do rigSafe rigb rig
               pure (Local v, ty, used rig)
    where
      rigSafe : RigCount -> RigCount -> Core annot ()
      rigSafe Rig1 RigW = throw (LinearMisuse loc x Rig1 RigW)
      rigSafe Rig0 RigW = throw (LinearMisuse loc x Rig0 RigW)
      rigSafe Rig0 Rig1 = throw (LinearMisuse loc x Rig0 Rig1)
      rigSafe _ _ = pure ()

      -- count the usage if we're in a linear context. If not, the usage doesn't
      -- matter
      used : RigCount -> Usage vars
      used Rig1 = [v]
      used _ = []

  lcheck loc rig env (Ref nt fn)
      = do gam <- getCtxt
           case lookupDefTyExact fn gam of
                Nothing => throw (InternalError ("Linearity checking failed on " ++ show fn))
                Just (def, ty) => pure (Ref nt fn, embed ty, [])

  lcheck loc rig env (Bind nm b sc)
      = do (b', bt, usedb) <- lcheckBinder loc rig env b
           (sc', sct, usedsc) <- lcheck loc rig (b' :: env) sc
           checkUsageOK (rigMult (multiplicity b) rig) usedsc
           pure $ discharge nm b' bt sc' sct (usedb ++ doneScope usedsc)
    where
      checkUsageOK : RigCount -> Usage (nm :: vars) -> Core annot ()
      checkUsageOK Rig0 _ = pure ()
      checkUsageOK RigW _ = pure ()
      checkUsageOK Rig1 ns 
          = let used = count Here ns in
                if used == 1 
                   then pure ()
                   else throw (LinearUsed loc used nm)

  lcheck loc rig env (App f a)
      = do (f', fty, fused) <- lcheck loc rig env f
           gam <- getCtxt
           case nf gam env fty of
                NBind _ (Pi rigf _ ty) scdone =>
                   do (a', aty, aused) <- lcheck loc (rigMult rigf rig) env a
                      let sc' = scdone (toClosure False env a')
                      pure (App f' a', quote gam env sc', fused ++ aused)
                _ => throw (InternalError ("Linearity checking failed on " ++ show f' ++ " (not a function)"))

  lcheck loc rig env (PrimVal x) = pure (PrimVal x, Erased, [])
  lcheck loc rig env Erased = pure (Erased, Erased, [])
  lcheck loc rig env TType = pure (TType, TType, [])

  lcheckBinder : {auto c : Ref Ctxt Defs} ->
                  annot -> RigCount -> Env Term vars -> 
                  Binder (Term vars) -> 
                  Core annot (Binder (Term vars), Term vars, Usage vars)
  lcheckBinder loc rig env (Lam c x ty)
      = do (tyv, tyt, _) <- lcheck loc Rig0 env ty
           pure (Lam c x tyv, tyt, [])
  lcheckBinder loc rig env (Let rigc val ty)
      = do (tyv, tyt, _) <- lcheck loc Rig0 env ty
           (valv, valt, vs) <- lcheck loc (rigMult rig rigc) env val
           pure (Let rigc valv tyv, tyt, vs)
  lcheckBinder loc rig env (Pi c x ty)
      = do (tyv, tyt, _) <- lcheck loc Rig0 env ty
           pure (Pi c x tyv, tyt, [])
  lcheckBinder loc rig env (PVar c ty)
      = do (tyv, tyt, _) <- lcheck loc Rig0 env ty
           pure (PVar c tyv, tyt, [])
  lcheckBinder loc rig env (PLet rigc val ty)
      = do (tyv, tyt, _) <- lcheck loc Rig0 env ty
           (valv, valt, vs) <- lcheck loc (rigMult rig rigc) env val
           pure (PLet rigc valv tyv, tyt, vs)
  lcheckBinder loc rig env (PVTy c ty)
      = do (tyv, tyt, _) <- lcheck loc Rig0 env ty
           pure (PVTy c tyv, tyt, [])
  
  discharge : (nm : Name) -> Binder (Term vars) -> Term vars ->
              Term (nm :: vars) -> Term (nm :: vars) -> Usage vars ->
              (Term vars, Term vars, Usage vars)
  discharge nm (Lam c x ty) bindty scope scopety used
       = (Bind nm (Lam c x ty) scope, Bind nm (Pi c x ty) scopety, used)
  discharge nm (Let c val ty) bindty scope scopety used
       = (Bind nm (Let c val ty) scope, Bind nm (Let c val ty) scopety, used)
  discharge nm (Pi c x ty) bindty scope scopety used
       = (Bind nm (Pi c x ty) scope, bindty, used)
  discharge nm (PVar c ty) bindty scope scopety used
       = (Bind nm (PVar c ty) scope, Bind nm (PVTy c ty) scopety, used)
  discharge nm (PLet c val ty) bindty scope scopety used
       = (Bind nm (PLet c val ty) scope, Bind nm (PLet c val ty) scopety, used)
  discharge nm (PVTy c ty) bindty scope scopety used
       = (Bind nm (PVTy c ty) scope, bindty, used)

bindEnv : Env Term vars -> (tm : Term vars) -> ClosedTerm
bindEnv [] tm = tm
bindEnv (b :: env) tm 
    = bindEnv env (Bind _ b tm)

export
linearCheck : {auto c : Ref Ctxt Defs} ->
              annot -> RigCount -> Env Term vars -> Term vars -> 
              Core annot ()
linearCheck loc rig env tm
    = do lcheck loc rig [] (bindEnv env tm)
         pure ()

