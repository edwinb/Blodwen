module TTImp.Elab

import Compiler.CompileExpr

import Core.CaseTree
import Core.Context
import Core.LinearCheck
import Core.Normalise
import Core.Reflect
import Core.TT
import Core.Unify

import TTImp.TTImp
import public TTImp.Elab.State
import public TTImp.Elab.Term

import Data.List
import Data.List.Views

%default covering

getRigNeeded : ElabMode -> RigCount
getRigNeeded InType = Rig0 -- unrestricted usage in types
getRigNeeded _ = Rig1

findPLetRenames : Term vars -> List (Name, Name)
findPLetRenames (Bind n (PLet c (Local {x = x@(MN _ _)} _ p) ty) sc)
    = (x, n) :: findPLetRenames sc
findPLetRenames (Bind n _ sc) = findPLetRenames sc
findPLetRenames tm = []

doPLetRenames : List (Name, Name) -> List Name -> Term vars -> Term vars
doPLetRenames ns drops (Bind n b@(PLet _ _ _) sc)
    = if n `elem` drops
         then subst Erased (doPLetRenames ns drops sc)
         else Bind n b (doPLetRenames ns drops sc)
doPLetRenames ns drops (Bind n b sc)
    = case lookup n ns of
           Just n' => Bind n' b (doPLetRenames ns (n' :: drops) (renameTop n' sc))
           Nothing => Bind n b (doPLetRenames ns drops sc)
doPLetRenames ns drops sc = sc

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
                                  log 5 $ "Substitued delayed hole " ++ show res
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
                        updateDef n (const (Just (PMDef True [] (STerm tm) (STerm tm))))
                        log 5 $ "Resolved delayed hole " ++ show n ++ " = " ++ show tm
                        removeHoleName n
                        pure True

elabTerm : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST (UState annot)} ->
           {auto i : Ref ImpST (ImpState annot)} ->
           Reflect annot =>
           Elaborator annot ->
           Name ->
           Env Term vars -> Env Term outer -> SubVars outer vars -> NestedNames vars ->
           ImplicitMode -> ElabMode ->
           (term : RawImp annot) ->
           (tyin : Maybe (Term vars)) ->
           Core annot (Term vars, -- checked term
                       Term vars, -- checked and erased term
                       Term vars) -- type
elabTerm {vars} process defining env env' sub nest impmode elabmode tm tyin
    = do resetHoles
         giveUpSearch -- reset from previous elaboration, if any
         e <- newRef EST (initEStateSub defining env' sub)
         let rigc = getRigNeeded elabmode
         (chktm_in, ty) <- check {e} rigc process (initElabInfo impmode elabmode) env nest tm tyin
         log 10 $ "Initial check: " ++ show chktm_in ++ " : " ++ show ty

         -- Final retry of constraints and delayed elaborations
         -- - Solve any constraints, then retry any delayed elaborations
         -- - Finally, last attempts at solving constraints, but this
         --   is most likely just to be able to display helpful errors
         solveConstraints (case elabmode of
                                InLHS => InLHS
                                _ => InTerm) Normal
         solveConstraints (case elabmode of
                                InLHS => InLHS
                                _ => InTerm) Normal
         gam <- get Ctxt
         chktm <- retryDelayedIn env (getAnnot tm) (normaliseHoles gam env chktm_in)
         log 10 $ "Check after delays: " ++ show chktm

         -- resolve any default hints
         solveConstraints (case elabmode of
                                InLHS => InLHS
                                _ => InTerm) Defaults
         -- perhaps resolving defaults helps...
         -- otherwise, this last go is most likely just to give us more
         -- helpful errors.
         solveConstraints (case elabmode of
                                InLHS => InLHS
                                _ => InTerm) LastChance

         dumpDots
         checkDots
         -- Bind the implicits and any unsolved holes they refer to
         -- This is in implicit mode 'PATTERN' and 'PI'
         fullImps <- getToBind env
         clearToBind -- remove the bound holes
         gam <- get Ctxt
         log 5 $ "Binding implicits " ++ show fullImps ++
                 " in " ++ show chktm
         est <- get EST
         let (restm, resty) = bindImplicits impmode gam env fullImps 
                                            (asVariables est) 
                                            chktm -- holes normalised already
                                            (normaliseHoles gam env ty)
         traverse implicitBind (map fst fullImps)
         -- Give implicit bindings their proper names, as UNs not PVs
         gam <- get Ctxt
         let ptm' = renameImplicits (gamma gam) restm
         let pty' = renameImplicits (gamma gam) resty
         log 5 $ "Elaboration result " ++ show ptm'
         log 5 $ "Elaboration result type " ++ show pty'

         normaliseHoleTypes
         clearSolvedHoles
         dumpConstraints 2 False
         checkUserHoles False -- need to fail if there are any guards
                              -- or 'linearCheck' will fail
         ptm' <- the (Core _ (Term vars)) $ case elabmode of
                    InLHS => pure ptm'
                    _ => do linearCheck (getAnnot tm) rigc False env ptm'
                            pure ptm'
         
         checkArgTypes (getAnnot tm) env ptm' -- Check no unsolved holes in argument types
         clearPatVars
         -- If there are remaining holes, we need to save them to the ttc
         -- since they haven't been normalised away yet, and they may be
         -- solved later
         hs <- getHoleNames
         traverse addToSave hs
         -- ...and we need to add their compiled forms, for any that might
         -- end up being executed
         traverse compileDef hs

         -- On the LHS, finish by tidying up the plets (changing things that
         -- were of the form x@_, where the _ is inferred to be a variable,
         -- to just x)
         case elabmode of
              InLHS => let vs = findPLetRenames ptm' in
                           do log 5 $ "Renamed PLets " ++ show (doPLetRenames vs [] ptm')
                              log 5 $ "Renamed PLets type " ++ show (doPLetRenames vs [] pty')
                              let ret = doPLetRenames vs [] ptm'
                              pure (ret, ret,
                                    doPLetRenames vs [] pty')
              _ => do perase <- linearCheck (getAnnot tm) rigc True env ptm'
                      pure (ptm', perase, pty')

export
inferTerm : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST (UState annot)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Reflect annot =>
            Elaborator annot -> 
            Name ->
            Env Term vars -> NestedNames vars ->
            ImplicitMode -> ElabMode ->
            (term : RawImp annot) ->
            Core annot (Term vars, Term vars, Term vars) 
inferTerm process defining env nest impmode elabmode tm 
    = elabTerm process defining env env SubRefl nest impmode elabmode tm Nothing

export
checkTerm : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST (UState annot)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Reflect annot =>
            Elaborator annot ->
            Name ->
            Env Term vars -> Env Term outer ->
            SubVars outer vars -> NestedNames vars ->
            ImplicitMode -> ElabMode ->
            (term : RawImp annot) -> (ty : Term vars) ->
            Core annot (Term vars, Term vars) 
checkTerm process defining env env' sub nest impmode elabmode tm ty 
    = do (tm_elab, tm_erase, _) <- elabTerm process defining env env' sub nest impmode elabmode tm (Just ty)
         pure (tm_elab, tm_erase)

