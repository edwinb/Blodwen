module Elab.Delayed

import Core.CaseTree
import Core.Context
import Core.Metadata
import Core.Normalise
import Core.TT
import Core.Unify

import Data.List

import TTImp.Elab.State
import TTImp.TTImp

-- Add whether the variable is used as a linear argument. Returns whether it
-- was added, so that we can stop as soon as it is
addUsage : {auto e : Ref EST (EState vars)} ->
           {auto c : Ref Ctxt Defs} ->
           Env Term vars -> annot -> Elem x vars -> Term vars -> Core annot Bool
addUsage env loc p (Local (Just Rig1) p')
    = do est <- get EST
         if sameVar p p'
            then do put EST (record { linearUsed $= ((_ ** p) :: ) } est)
                    pure True
            else pure False
addUsage {vars} {x} {e} env loc p (Bind n b sc)
    = do added <- addUsageB p b
         if added then pure True
                  else do e' <- weakenedEState
                          let env' : Env Term (n :: _) = b :: env
                          u <- addUsage {e=e'} env' loc (There p) sc
                          st' <- strengthenedEState {e=e'} False loc env'
                          put {ref=e} EST st'
                          pure u
  where
    addUsageB : Elem x vars -> Binder (Term vars) -> Core annot Bool
    addUsageB p (Let c val ty) 
        = addUsage env loc p val
    addUsageB p (PLet c val ty) 
        = addUsage env loc p val
    addUsageB p _ = pure False

addUsage env loc p (App f a) 
    = do added <- addUsage env loc p f
         if added then pure True
                  else addUsage env loc p a
addUsage env loc p tm = pure False

mutual
  export
  retryDelayedIn :
        {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
        {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
        Env Term vars -> annot -> Term vars -> Core annot (Term vars)
  retryDelayedIn env loc (Ref nt n)
      = do defs <- get Ctxt
           case lookupDefExact n (gamma defs) of
                Just Delayed => 
                    do ok <- runDelayed loc n
                       -- On success, substitute the result in, and go 
                       -- around again,
                       if ok
                          then do defs <- get Ctxt
                                  let tm' = normaliseHoles defs env (Ref nt n)
                                  res <- retryDelayedIn env loc tm'
                                  log 5 $ "Substituted delayed hole " ++ show res
                                  pure res
                          else pure (Ref nt n)
                _ => pure (Ref nt n)
  retryDelayedIn {vars} {e} env loc (Bind x b sc)
      = do b' <- retryBinder env b
           e' <- weakenedEState
           let env' : Env Term (x :: _) = b :: env
           -- We'll only need to worry about multiplicities if the binder
           -- is linear... if it's linear, add whether it's used to the
           -- state, then when we get to the delayed elaborators for case
           -- blocks the usage information will be up to date
           when (multiplicity b == Rig1) $
                do addUsage {e=e'} env' loc Here sc
                   pure ()
           sc' <- retryDelayedIn {e=e'} env' loc sc
           st' <- strengthenedEState {e=e'} False loc env'
           put {ref=e} EST st'
           pure (Bind x b' sc')
    where
      retryBinder : Env Term vars -> Binder (Term vars) -> 
                    Core annot (Binder (Term vars))
      retryBinder env (Lam c p ty)
          = do ty' <- retryDelayedIn env loc ty
               pure (Lam c p ty')
      retryBinder env (Let c val ty)
          = do val' <- retryDelayedIn env loc val
               ty' <- retryDelayedIn env loc ty
               pure (Let c val' ty')
      retryBinder env (Pi c p ty)
          = do ty' <- retryDelayedIn env loc ty
               pure (Pi c p ty')
      retryBinder env (PVar c ty)
          = do ty' <- retryDelayedIn env loc ty
               pure (PVar c ty')
      retryBinder env (PLet c val ty)
          = do val' <- retryDelayedIn env loc val
               ty' <- retryDelayedIn env loc ty
               pure (PLet c val' ty')
      retryBinder env (PVTy c ty)
          = do ty' <- retryDelayedIn env loc ty
               pure (PVTy c ty')
  retryDelayedIn env loc (App f a)
      = do f' <- retryDelayedIn env loc f
           a' <- retryDelayedIn env loc a
           pure (App f' a')
  retryDelayedIn env loc tm = pure tm

  runDelayed :
        {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
        {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
        annot -> Name -> Core annot Bool
  runDelayed loc n
      = do ust <- get UST
           case lookupCtxtExact n (delayedElab ust) of
                Nothing => pure False
                Just elab =>
                     do tm <- elab
                        updateDef n (const (Just (PMDef True [] (STerm tm) (STerm tm) [])))
                        log 5 $ "Resolved delayed hole " ++ show n ++ " = " ++ show tm
                        removeHoleName n
                        pure True

-- We run the elaborator in the given environment, but need to end up with a
-- closed term. It'll get substituted into the right place at the end of
-- elaboration, so here we're just lambda binding the names so that the
-- substitution is successful.
total
mkClosedElab : Env Term vars -> 
               (Core annot (Term vars, Term vars)) ->
               Core annot ClosedTerm
mkClosedElab [] elab 
    = do (tm, _) <- elab
         pure tm
mkClosedElab {vars = x :: vars} (b :: env) elab
    = mkClosedElab env 
          (do (sc', _) <- elab
              pure (Bind x (Lam (multiplicity b) Explicit (binderType b)) sc', 
                    Erased))

-- Try the given elaborator; if it fails, and the error matches the
-- predicate, make a hole and try it again later when more holes might
-- have been resolved
export
delayOnFailure : 
      {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
      {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
      {auto m : Ref Meta (Metadata annot)} ->
      annot -> Env Term vars ->
      (expected : Term vars) ->
      (Error annot -> Bool) ->
      (Bool -> Core annot (Term vars, Term vars)) ->
      Core annot (Term vars, Term vars)
delayOnFailure loc env expected pred elab 
    = handle (elab False)
        (\err => do if pred err 
                        then 
                          do (cn, dty) <- addDelayedElab loc env expected
                             log 5 $ "Postponing elaborator for " ++ show expected
                             log 5 $ "New hole type " ++ show cn ++ " : " ++ show dty
                             ust <- get UST
                             put UST (record { delayedElab $= addCtxt cn
                                                 (mkClosedElab env (elab True)) } ust)
                             pure (mkConstantAppFull cn env, expected)
                        else throw err)

export
delayElab : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
            {auto m : Ref Meta (Metadata annot)} ->
            annot -> Env Term vars ->
            (expected : ExpType (Term vars)) ->
            Lazy (Core annot (Term vars, Term vars)) ->
            Core annot (Term vars, Term vars)
delayElab {vars} loc env expected elab
    = do exp <- mkExpected expected
         (cn, dty) <- addDelayedElab loc env exp
         log 5 $ "Postponing elaborator for " ++ show exp
         log 5 $ "New hole type " ++ show cn ++ " : " ++ show dty
         ust <- get UST
         put UST (record { delayedElab $= addCtxt cn
                             (mkClosedElab env elab) } ust)
         pure (mkConstantAppFull cn env, exp)
  where
    mkExpected : ExpType (Term vars) -> Core annot (Term vars)
    mkExpected (FnType [] ty) = pure ty
    mkExpected _
        = do t <- addHole loc env TType "delayty"
             pure (mkConstantApp t env)


