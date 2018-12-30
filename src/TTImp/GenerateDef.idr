module TTImp.GenerateDef

-- Attempt to generate a complete definition from a type

import Core.Context
import Core.Metadata
import Core.Normalise
import Core.TT
import Core.Unify
import Control.Monad.StateE
import Control.Catchable

import TTImp.CaseSplit
import TTImp.Elab
import TTImp.Elab.Unelab
import TTImp.ExprSearch
import TTImp.ProcessDef
import TTImp.ProcessTTImp
import TTImp.Reflect
import TTImp.TTImp
import TTImp.Utils

%default covering

mutual
  fnGenName : Bool -> GenName -> String
  fnGenName lhs (Nested _ n) = fnName lhs n
  fnGenName lhs (CaseBlock n _) = fnName lhs n
  fnGenName lhs (WithBlock n _) = fnName lhs n

  fnName : Bool -> Name -> String
  fnName lhs (UN n) 
      = if any (not . identChar) (unpack n)
           then if lhs then "(" ++ n ++ ")"
                       else "op"
           else n
  fnName lhs (NS _ n) = fnName lhs n
  fnName lhs (DN s _) = s
  fnName lhs (GN g) = fnGenName lhs g
  fnName lhs n = show n

getEnvArgNames : Defs -> Nat -> NF [] -> List String
getEnvArgNames defs Z sc = getArgNames defs [] [] sc
getEnvArgNames defs (S k) (NBind n _ sc)
    = getEnvArgNames defs k (sc (MkClosure defaultOpts [] [] Erased))
getEnvArgNames defs n ty = []

expandClause : {auto c : Ref Ctxt Defs} ->
               {auto m : Ref Meta (Metadata annot)} ->
               {auto u : Ref UST (UState annot)} ->
               {auto i : Ref ImpST (ImpState annot)} ->
               (Reflect annot, Reify annot) =>
               annot -> Elaborator annot -> Name -> ImpClause annot -> 
               Core annot (List (ImpClause annot))
expandClause loc elab n c
    = do Just (clause, _) <- checkClause elab False rig1 False n [] (MkNested []) c
            | Nothing => pure [] -- TODO: impossible clause, do something
                                 -- appropriate
         let MkClause {vars} env lhs rhs = clause
         log 5 $ show vars ++ " " ++ show lhs ++ " = " ++ show rhs
         let Ref Func n = getFn rhs
            | _ => throw (GenericMsg loc "No searchable hole on RHS")
         defs <- get Ctxt
         let Just (Hole locs _ _) = lookupDefExact n (gamma defs)
            | _ => throw (GenericMsg loc "No searchable hole on RHS")
         (rhs' :: _) <- exprSearch loc n []
            | _ => throw (GenericMsg loc "No result found for search on RHS")
         defs <- get Ctxt
         let rhsnf = normaliseHoles defs [] rhs'
         let (_ ** (env, rhsenv)) = dropLams locs [] rhsnf

         rhsraw <- unelab loc env rhsenv 
         log 5 $ "Got clause " ++ show lhs ++ " = " ++ show rhsenv
         pure [updateRHS c rhsraw]
  where
    updateRHS : ImpClause annot -> RawImp annot -> ImpClause annot
    updateRHS (PatClause fc lhs _) rhs = PatClause fc lhs rhs
    -- 'with' won't happen, include for completeness
    updateRHS (WithClause fc lhs wval cs) rhs = WithClause fc lhs wval cs
    updateRHS (ImpossibleClause fc lhs) _ = ImpossibleClause fc lhs

    dropLams : Nat -> Env Term vars -> Term vars -> 
               (vars' ** (Env Term vars', Term vars'))
    dropLams Z env tm = (_ ** (env, tm))
    dropLams (S k) env (Bind _ b sc) = dropLams k (b :: env) sc 
    dropLams _ env tm = (_ ** (env, tm))

splittableNames : RawImp annot -> List Name
splittableNames (IApp _ f (IBindVar _ n))
    = splittableNames f ++ [UN n]
splittableNames (IApp _ f _)
    = splittableNames f
splittableNames (IImplicitApp _ f _ _)
    = splittableNames f
splittableNames _ = []

trySplit : {auto m : Ref Meta (Metadata annot)} ->
           {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST (UState annot)} ->
           (Reflect annot, Reify annot) =>
           annot -> RawImp annot -> ClosedTerm -> RawImp annot -> Name ->
           Core annot (Name, List (ImpClause annot))
trySplit loc lhsraw lhs rhs n
    = do OK updates <- getSplitsLHS loc 0 lhs n
            | _ => pure (n, [])
         pure (n, map (\ups => PatClause loc (updateLHS ups lhsraw) rhs) 
                      (mapMaybe valid updates))
  where
    valid : ClauseUpdate annot -> Maybe (List (Name, RawImp annot))
    valid (Valid lhs' ups) = Just ups
    valid _ = Nothing

    fixNames : RawImp annot -> RawImp annot
    fixNames (IVar loc' (UN n)) = IBindVar loc' n
    fixNames (IVar loc' (MN _ _)) = Implicit loc'
    fixNames (IApp loc' f a) = IApp loc' (fixNames f) (fixNames a)
    fixNames (IImplicitApp loc' f t a) = IImplicitApp loc' (fixNames f) t (fixNames a)
    fixNames tm = tm

    updateLHS : List (Name, RawImp annot) -> RawImp annot -> RawImp annot
    updateLHS ups (IVar loc' n)
        = case lookup n ups of
               Nothing => IVar loc' n
               Just tm => fixNames tm
    updateLHS ups (IBindVar loc' n)
        = case lookup (UN n) ups of
               Nothing => IBindVar loc' n
               Just tm => fixNames tm
    updateLHS ups (IApp loc' f a) = IApp loc' (updateLHS ups f) (updateLHS ups a)
    updateLHS ups (IImplicitApp loc' f t a) 
        = IImplicitApp loc' (updateLHS ups f) t (updateLHS ups a)
    updateLHS ups tm = tm

generateSplits : {auto m : Ref Meta (Metadata annot)} ->
                 {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST (UState annot)} ->
                 {auto i : Ref ImpST (ImpState annot)} ->
                 (Reflect annot, Reify annot) =>
                 annot -> Name -> ImpClause annot -> 
                 Core annot (List (Name, List (ImpClause annot)))
generateSplits loc fn (ImpossibleClause fc lhs) = pure []
generateSplits loc fn (WithClause fc lhs wval cs) = pure []
generateSplits {c} {u} {i} {m} loc fn (PatClause fc lhs rhs) 
    = do (lhstm, _, _) <- inferTerm {c} {u} {i} {m}
                                        (\c, u, i, m => processDecl {c} {u} {i} {m})
                                        False fn [] (MkNested [])
                                        PATTERN (InLHS rig1) lhs
         traverse (trySplit fc lhs lhstm rhs) (splittableNames lhs)

mutual
  tryAllSplits : {auto c : Ref Ctxt Defs} ->
                 {auto m : Ref Meta (Metadata annot)} ->
                 {auto u : Ref UST (UState annot)} ->
                 {auto i : Ref ImpST (ImpState annot)} ->
                 (Reflect annot, Reify annot) =>
                 annot -> Elaborator annot -> Name -> Error annot ->
                 List (Name, List (ImpClause annot)) -> 
                 Core annot (List (ImpClause annot))
  tryAllSplits loc elab n err [] = throw err
  tryAllSplits loc elab n err ((x, []) :: rest) 
      = tryAllSplits loc elab n err rest
  tryAllSplits loc elab n err ((x, cs) :: rest)
      = do log 5 $ "Splitting on " ++ show x
           catch (do cs' <- traverse (mkSplits loc elab n) cs
                     pure (concat cs'))
                 (\err => tryAllSplits loc elab n err rest)

  mkSplits : {auto c : Ref Ctxt Defs} ->
             {auto m : Ref Meta (Metadata annot)} ->
             {auto u : Ref UST (UState annot)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             (Reflect annot, Reify annot) =>
             annot -> Elaborator annot -> Name -> ImpClause annot -> 
             Core annot (List (ImpClause annot))
  -- If the clause works, use it. Otherwise, split on one of the splittable
  -- variables and try all of the resulting clauses
  mkSplits loc elab n c
      = catch (expandClause loc elab n c)
          (\err =>
              do cs <- generateSplits loc n c
                 log 5 $ "Splits: " ++ show cs
                 tryAllSplits loc elab n err cs)

export
makeDef : {auto c : Ref Ctxt Defs} ->
          {auto m : Ref Meta (Metadata annot)} ->
          {auto u : Ref UST (UState annot)} ->
          (Reflect annot, Reify annot) =>
          (annot -> (Name, Nat, ClosedTerm) -> Bool) -> 
          Name -> Core annot (Maybe (annot, List (ImpClause annot)))
makeDef p n 
    = do Just (loc, n, envlen, ty) <- findTyDeclAt p
            | Nothing => pure Nothing
         defs <- get Ctxt
         meta <- get Meta
         ust <- get UST
         let argns = getEnvArgNames defs envlen (nf defs [] ty)
         -- Need to add implicit patterns for the outer environment.
         -- We won't try splitting on these
         let pre_env = replicate envlen (Implicit loc) 

         let rhshole = uniqueName defs [] (fnName False n ++ "_rhs")
         let initcs = PatClause loc 
                            (apply (IVar loc n) (pre_env ++ (map (IBindVar loc) argns)))
                            (IHole loc rhshole)
         i <- newRef ImpST (initImpState {annot})
         cs' <- mkSplits loc (\ c, u, i, m => processDecl {c} {u} {i} {m})
                             n initcs
         -- restore the global state, given that we've fiddled with it a lot!
         put Ctxt defs
         put Meta meta
         put UST ust
         pure (Just (loc, cs'))

