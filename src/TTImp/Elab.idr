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
         e <- newRef EST (initEStateSub defining env' sub)
         let rigc = getRigNeeded elabmode
         (chktm, ty) <- check {e} rigc process (initElabInfo impmode elabmode) env nest tm tyin
         log 10 $ "Initial check: " ++ show chktm ++ " : " ++ show ty

         -- Final retry of constraints and delayed elaborations
         -- - Solve any constraints, then retry any delayed elaborations
         -- - Finally, last attempts at solving constraints, but this
         --   is most likely just to be able to display helpful errors
         solveConstraints (case elabmode of
                                InLHS => InLHS
                                _ => InTerm) Normal
         retryAllDelayed
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
                                            (asVariables est) chktm ty
         traverse implicitBind (map fst fullImps)
         -- Give implicit bindings their proper names, as UNs not PVs
         gam <- get Ctxt
         let ptm' = renameImplicits (gamma gam) (normaliseHoles gam env restm)
         let pty' = renameImplicits (gamma gam) resty
         log 5 $ "Elaboration result " ++ show ptm'

         normaliseHoleTypes
         clearSolvedHoles
         dumpConstraints 2 False
         checkUserHoles False -- need to fail if there are any guards
                              -- or 'linearCheck' will fail
         ptm' <- the (Core _ (Term vars)) $ case elabmode of
                    InLHS => pure ptm'
                    _ => do linearCheck (getAnnot tm) rigc False env ptm'
                            pure ptm'
         
         checkArgTypes (getAnnot tm) ptm' -- Check no unsolved holes in argument types
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

