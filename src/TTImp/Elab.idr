module TTImp.Elab

import TTImp.TTImp
import public TTImp.Elab.State
import public TTImp.Elab.Term
import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT
import Core.Typecheck
import Core.Unify

import Data.List
import Data.List.Views

%default covering

elabTerm : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST (UState annot)} ->
           {auto i : Ref ImpST (ImpState annot)} ->
           Elaborator annot ->
           Name ->
           Env Term vars -> NestedNames vars ->
           ImplicitMode -> ElabMode ->
           (term : RawImp annot) ->
           (tyin : Maybe (Term vars)) ->
           Core annot (Term vars, Term vars) 
elabTerm process defining env nest impmode elabmode tm tyin
    = do resetHoles
         e <- newRef EST (initEState defining)
         (chktm, ty) <- check {e} process (initElabInfo impmode elabmode) env nest tm tyin
         log 10 $ "Initial check: " ++ show chktm ++ " : " ++ show ty
         solveConstraints (case elabmode of
                                InLHS => InLHS
                                _ => InTerm)
         dumpDots
         checkDots
         est <- get EST
         -- Bind the implicits and any unsolved holes they refer to
         -- This is in implicit mode 'PATTERN' and 'PI'
         let fullImps = reverse $ toBind est
         clearToBind -- remove the bound holes
         gam <- getCtxt
         log 5 $ "Binding implicits " ++ show (dropTmIn fullImps) ++
                 " in " ++ show chktm
         let (restm, resty) = bindImplicits impmode gam env
                                            (dropTmIn fullImps) chktm ty
         traverse implicitBind (map fst fullImps)
         gam <- getCtxt
         (ptm, pty, bound) <- findHoles impmode env (normaliseHoles gam env restm) resty
         -- Give implicit bindings their proper names, as UNs not PVs
         gam <- getCtxt
         let ptm' = renameImplicits gam ptm
         let pty' = renameImplicits gam pty
         -- Drop any holes we created which aren't used in the resulting
         -- term
         traverse (\n => implicitBind n) bound
         dumpConstraints 2 False
         pure (ptm', pty')

export
inferTerm : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST (UState annot)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot -> 
            Name ->
            Env Term vars -> NestedNames vars ->
            ImplicitMode -> ElabMode ->
            (term : RawImp annot) ->
            Core annot (Term vars, Term vars) 
inferTerm process defining env nest impmode elabmode tm 
    = elabTerm process defining env nest impmode elabmode tm Nothing

export
checkTerm : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST (UState annot)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot ->
            Name ->
            Env Term vars -> NestedNames vars ->
            ImplicitMode -> ElabMode ->
            (term : RawImp annot) -> (ty : Term vars) ->
            Core annot (Term vars) 
checkTerm process defining env nest impmode elabmode tm ty 
    = do (tm_elab, _) <- elabTerm process defining env nest impmode elabmode tm (Just ty)
         pure tm_elab

