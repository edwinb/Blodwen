module Core.AutoSearch

-- Proof search for auto implicits and interface implementations

import Core.Context
import Core.TT
import Core.CaseTree
import Core.Normalise
import Core.Unify

import Data.List

%default covering

trivial : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState annot)} ->
          annot -> Env Term vars -> Term vars -> Core annot (Term vars)
trivial loc [] ty = throw (CantSolveGoal loc [] ty)
trivial {vars = v :: vs} loc (b :: env) ty 
-- If the type of the variable at the top of the environment converts with
-- the goal, use it (converts, not unifying, so no solving metavariables here)
    = try (do gam <- get Ctxt
              let bty = binderType b
              if convert gam (b :: env) (weaken bty) ty
                 then do log 6 $ "Trivial success: " ++ show v ++ " : " ++ show (weaken {n = v} bty)
                                     ++ " for " ++ show ty
                         pure (Local Here)
                 else do log 7 $ "Trivial fail: " ++ show v ++ " : " ++ show (weaken {n = v} bty)
                                     ++ " for " ++ show ty
                         throw (CantSolveGoal loc (b :: env) ty))
          (case shrinkTerm ty (DropCons SubRefl) of
                Nothing => throw (CantSolveGoal loc (b :: env) ty)
                Just ty' => do tm' <- trivial loc env ty'
                               pure (weaken tm'))

mkArgs : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST (UState annot)} ->
         annot -> Env Term vars -> Term vars -> 
         Core annot (List (Name, Term vars), Term vars)
mkArgs loc env (Bind n (Pi c info ty) sc)
    = do argName <- addHole loc env ty
         let arg = mkConstantApp argName env
         (rest, restTy) <- mkArgs loc env (subst arg sc)
         pure ((argName, arg) :: rest, restTy)
mkArgs loc env ty = pure ([], ty)

nameIsHole : {auto c : Ref Ctxt Defs} ->
             annot -> Name -> Core annot Bool
nameIsHole loc n
    = do gam <- get Ctxt
         case lookupDefExact n (gamma gam) of
              Nothing => throw (InternalError "Can't happen, name has mysteriously vanised")
              Just def =>
                   case def of
                        Hole locs False => pure True
                        _ => pure False

-- Search recursively, but only if the given name wasn't solved by unification
searchIfHole : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState annot)} ->
               annot -> Nat -> List ClosedTerm ->
               Name -> Name -> Core annot ()
searchIfHole loc Z trying defining n = throw (InternalError "Search depth limit reached")
searchIfHole loc (S depth) trying defining n
    = if !(nameIsHole loc n) 
         then do search loc depth trying defining n
                 pure ()
         else pure ()

-- Apply the name to arguments and see if the result unifies with the target
-- type, then try to automatically solve any holes which were generated.
-- If there are any remaining holes, search fails.
searchName : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Nat -> List ClosedTerm ->
             Env Term vars -> NF vars -> Name -> Name -> Core annot (Term vars)
searchName loc depth trying env ty defining con
    = do gam <- get Ctxt
         case lookupDefTyExact con (gamma gam) of
              Just (DCon tag arity _, cty)
                  => do let nty = normalise gam [] cty
                        (args, appTy) <- mkArgs loc env (embed nty)
                        [] <- unify InTerm loc env ty (nf gam env appTy)
                              | _ => throw (CantSolveGoal loc env (quote gam env ty))
                        let candidate = apply (Ref (DataCon tag arity) con)
                                              (map snd args)
                        -- TODO: Go through the arguments and solve them, if they
                        -- haven't been solved by unification
                        traverse (searchIfHole loc depth trying defining) (map fst args)
                        pure candidate
              Just (_, cty)
                  => do let nty = normalise gam [] cty
                        ctxt <- get Ctxt
                        let arity = getArity ctxt [] cty

                        (args, appTy) <- mkArgs loc env (embed nty)
                        [] <- unify InTerm loc env ty (nf gam env appTy)
                              | _ => throw (CantSolveGoal loc env (quote gam env ty))
                        let candidate = apply (Ref Func con) (map snd args)
                        -- TODO: Go through the arguments and solve them, if they
                        -- haven't been solved by unification
                        traverse (searchIfHole loc depth trying defining) (map fst args)
                        pure candidate
              _ => throw (CantSolveGoal loc env (quote gam env ty))

searchNames : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              annot -> Nat -> List ClosedTerm -> Env Term vars -> NF vars -> 
              Name -> List Name -> Core annot (Term vars)
searchNames loc depth trying env ty defining []
    = do gam <- get Ctxt
         throw (CantSolveGoal loc env (quote gam env ty))
searchNames loc depth trying env ty defining (n :: ns)
    = do gam <- get Ctxt
         log 5 $ "Searching " ++ show n ++ " for " ++ show (quote gam env ty)
         handleError (searchName loc depth trying env ty defining n)
           (\err => searchNames loc depth trying env ty defining ns)

-- Fail with the given error if any of the determining arguments are holes
concreteDets : {auto c : Ref Ctxt Defs} ->
               annot -> Nat -> List Nat -> Lazy (Error annot) -> 
               List (Closure vars) -> Core annot ()
concreteDets loc i ds err [] = pure ()
concreteDets loc i ds err (cl :: cs)
    = if not (i `elem` ds) 
         then concreteDets loc (1 + i) ds err cs
         else do defs <- get Ctxt
                 case evalClosure defs cl of
                      -- if 'hn' is a hole, we can't proceed yet
                      NApp (NRef _ hn) args =>
                           do hole <- nameIsHole loc hn
                              if hole
                                 then throw (Force err)
                                 else concreteDets loc (1 + i) ds err cs
                      _ => concreteDets loc (1 + i) ds err cs

-- Type directed search - take the first thing of the given type it finds using
-- the current environment.
searchType : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Nat -> List ClosedTerm -> Env Term vars -> Name ->
             NF vars -> Core annot (Term vars)
searchType loc depth trying env defining (NBind n (Pi c info ty) scfn)
    = do xn <- genName "x"
         gam <- get Ctxt
         let env' : Env Term (n :: _) = Pi c info (quote (noGam gam) env ty) :: env
         let sc = scfn (toClosure False env (Ref Bound xn))
         let tmsc = refToLocal xn n (quote (noGam gam) env sc)
         log 6 $ "Introduced lambda, search for " ++ show (normalise gam env' tmsc)
         scVal <- searchType loc depth trying env' defining (nf gam env' tmsc)
         pure (Bind n (Lam c info (quote (noGam gam) env ty)) scVal)
searchType loc depth trying env defining ty@(NTCon n t ar args)
    = do gam <- get Ctxt
         if length args == ar
           then do (dets, allCons) <- getSearchData loc n
                   let cons = filter (/=defining) allCons
                   concreteDets loc 0 dets 
                                (CantSolveGoal loc env (quote gam env ty)) 
                                args
                   log 5 $ "Hints for " ++ show n ++ ": " ++ show cons
                   try (trivial loc env (quote (noGam gam) env ty))
                       (searchNames loc depth trying env ty defining cons)
           else throw (CantSolveGoal loc env (quote gam env ty))
searchType loc depth trying env defining (NPrimVal IntType)
    = pure (PrimVal (I 0))
searchType loc depth trying env defining ty 
    = do gam <- get Ctxt
         try (trivial loc env (quote (noGam gam) env ty))
             (throw (CantSolveGoal loc env (quote gam env ty)))

abandonIfCycle : {auto c : Ref Ctxt Defs} ->
                 ClosedTerm -> List ClosedTerm -> Core annot ()
abandonIfCycle tm [] = pure ()
abandonIfCycle tm (ty :: tys)
    = do defs <- get Ctxt
         if convert defs [] tm ty
            then throw (InternalError "Cycle in search")
            else abandonIfCycle tm tys

searchHole : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Nat -> List ClosedTerm ->
             Name -> Name -> Defs -> GlobalDef -> Core annot ClosedTerm
searchHole loc depth trying defining n gam glob
    = do let searchty = normaliseHoles gam [] (type glob)
         abandonIfCycle searchty trying
         let nty = nf gam [] searchty
         log 5 $ "Running search: " ++ show n ++ " in " ++ show defining ++
                 " for " ++ show (quote gam [] nty)
         soln <- searchType loc depth (searchty :: trying) [] defining nty
         log 5 $ "Solution: " ++ show n ++ " = " ++ show (normalise gam [] soln)
         addDef n (record { definition = PMDef True [] (STerm soln) } glob)
         removeHoleName n
         pure soln

-- Declared in Unify.idr (please remember to keep this type up to date!)
-- search : {auto c : Ref Ctxt Defs} ->
--          {auto u : Ref UST (UState annot)} ->
--          annot -> Nat -> Name -> Name -> Core annot ClosedTerm
Core.Unify.search loc depth trying defining n_in
    = do gam <- get Ctxt
         case lookupHoleName n_in (gamma gam) of
              Just (n, glob) =>
                   -- The definition should be 'BySearch' at this stage,
                   -- if it's arising from an auto implicit
                   case definition glob of
                        Hole locs False => searchHole loc depth trying defining n gam glob
                        BySearch _ _ => searchHole loc depth trying defining n gam glob
                        _ => throw (InternalError $ "Not a hole: " ++ show n ++ " in " ++ show defining)
              _ => throw (UndefinedName loc n_in)
  where
    lookupHoleName : Name -> Gamma -> Maybe (Name, GlobalDef)
    lookupHoleName n gam
        = case lookupGlobalExact n gam of
               Just res => Just (n, res)
               Nothing => case lookupGlobalName n gam of
                               [res] => Just res
                               _ => Nothing
