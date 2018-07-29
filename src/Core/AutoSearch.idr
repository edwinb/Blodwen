module Core.AutoSearch

-- Proof search for auto implicits and interface implementations

import Core.Context
import Core.TT
import Core.CaseTree
import Core.Normalise
import Core.Unify

import Data.List

%default covering

mkTmArgs : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST (UState annot)} ->
           annot -> Env Term vars -> Term vars -> 
           Core annot (List (Name, Term vars), Term vars)
mkTmArgs loc env (Bind n (Pi c info ty) sc)
    = do argName <- genName "sa"
         addNamedHole loc argName False env ty
         let arg = mkConstantApp argName env
         (rest, restTy) <- mkTmArgs loc env (subst arg sc)
         pure ((argName, arg) :: rest, restTy)
mkTmArgs loc env ty = pure ([], ty)

mkArgs : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST (UState annot)} ->
         annot -> Env Term vars -> NF vars -> 
         Core annot (List (Name, Term vars), NF vars)
mkArgs loc env (NBind n (Pi c info ty) sc)
    = do gam <- get Ctxt
         argName <- genName "sa"
         addNamedHole loc argName False env (quote (noGam gam) env ty)
         let arg = mkConstantApp argName env
         (rest, restTy) <- mkArgs loc env (sc (MkClosure False [] env Erased))
         pure ((argName, arg) :: rest, restTy)
mkArgs loc env ty = pure ([], ty)

getAllEnv : (done : List Name) -> 
            Env Term vars -> List (Term (done ++ vars), Term (done ++ vars))
getAllEnv done [] = []
getAllEnv {vars = v :: vs} done (b :: env) 
   = let rest = getAllEnv (done ++ [v]) env in
         (Local (weakenElem {ns = done} Here), 
           rewrite appendAssociative done [v] vs in 
              weakenNs (done ++ [v]) (binderType b)) :: 
                   rewrite appendAssociative done [v] vs in rest

nameIsHole : {auto c : Ref Ctxt Defs} ->
             annot -> Name -> Core annot Bool
nameIsHole loc n
    = do gam <- get Ctxt
         case lookupDefExact n (gamma gam) of
              Nothing => throw (InternalError "Can't happen, name has mysteriously vanished")
              Just def =>
                   case def of
                        Hole locs False _ => pure True
                        _ => pure False

-- Search recursively, but only if the given name wasn't solved by unification
searchIfHole : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState annot)} ->
               annot -> Bool -> Nat -> List ClosedTerm ->
               Name -> Name -> Core annot ()
searchIfHole loc defaults Z trying defining n = throw (InternalError "Search depth limit reached")
searchIfHole loc defaults (S depth) trying defining n
    = if !(nameIsHole loc n) 
         then do search loc defaults depth trying defining n
                 pure ()
         else pure ()

-- Apply the name to arguments and see if the result unifies with the target
-- type, then try to automatically solve any holes which were generated.
-- If there are any remaining holes, search fails.
searchName : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Bool -> Nat -> List ClosedTerm ->
             Env Term vars -> NF vars -> Name -> Name -> Core annot (Term vars)
searchName loc defaults depth trying env ty defining con
    = do gam <- get Ctxt
         case lookupDefTyExact con (gamma gam) of
              Just (DCon tag arity _, cty)
                  => do let nty = normalise gam [] cty
                        (args, appTy) <- mkTmArgs loc env (embed nty)
                        [] <- unify InTerm loc env ty (nf gam env appTy)
                              | _ => throw (CantSolveGoal loc env (quote gam env ty))
                        let candidate = apply (Ref (DataCon tag arity) con)
                                              (map snd args)
                        -- Go through the arguments and solve them, if they
                        -- haven't been solved by unification
                        traverse (searchIfHole loc defaults depth trying defining) (map fst args)
                        pure candidate
              Just (_, cty)
                  => do let nty = normalise gam [] cty
                        ctxt <- get Ctxt
                        (args, appTy) <- mkTmArgs loc env (embed nty)
                        [] <- unify InTerm loc env ty (nf gam env appTy)
                              | _ => throw (CantSolveGoal loc env (quote gam env ty))
                        let candidate = apply (Ref Func con) (map snd args)
                        -- Go through the arguments and solve them, if they
                        -- haven't been solved by unification
                        traverse (searchIfHole loc defaults depth trying defining) (map fst args)
                        pure candidate
              _ => throw (CantSolveGoal loc env (quote gam env ty))

successful : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             List (Core annot (Term vars)) ->
             Core annot (List (Either (Error annot) (Term vars, Defs, UState annot)))
successful [] = pure []
successful (elab :: elabs)
    = do st <- get Ctxt
         ust <- get UST
         catch (do res <- elab
                   st' <- get Ctxt
                   ust' <- get UST
                   put Ctxt st
                   put UST ust
                   rest <- successful elabs
                   pure (Right (res, st', ust') :: rest))
               (\err => do put Ctxt st
                           put UST ust
                           rest <- successful elabs
                           pure (Left err :: rest))

exactlyOne : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Env Term vars -> NF vars -> 
             List (Core annot (Term vars)) ->
             Core annot (Term vars)
exactlyOne loc env ty [elab] = elab
exactlyOne loc env ty all
    = do elabs <- successful all
         case rights elabs of
              [(res, state, ust)] => do put Ctxt state
                                        put UST ust
                                        pure res
              [] => do gam <- get Ctxt
                       throw (CantSolveGoal loc env (quote gam env ty))
              rs => throw (AmbiguousSearch loc (map fst rs))

anyOne : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST (UState annot)} ->
         annot -> Env Term vars -> NF vars ->
         List (Core annot (Term vars)) ->
         Core annot (Term vars)
anyOne loc env ty [] = do gam <- get Ctxt
                          throw (CantSolveGoal loc env (quote gam env ty))
anyOne loc env ty [elab] = elab
anyOne loc env ty (e :: es) = try e (anyOne loc env ty es)

searchNames : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              annot -> Bool -> Nat -> List ClosedTerm -> Env Term vars -> NF vars -> 
              Name -> List Name -> Core annot (Term vars)
searchNames loc defaults depth trying env ty defining []
    = do gam <- get Ctxt
         throw (CantSolveGoal loc env (quote gam env ty))
searchNames loc defaults depth trying env ty defining (n :: ns)
    = do gam <- get Ctxt
         log 5 $ "Searching " ++ show (n :: ns) ++ " for " ++ show (quote gam env ty)
         exactlyOne loc env ty 
            (map (searchName loc defaults depth trying env ty defining) (n :: ns))

searchLocalWith : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST (UState annot)} ->
                  annot -> Bool -> Nat -> List ClosedTerm ->
                  Env Term vars -> List (Term vars, Term vars) ->
                  Term vars -> Name -> Core annot (Term vars)
searchLocalWith loc defaults depth trying env [] ty defining
    = throw (CantSolveGoal loc env ty)
searchLocalWith {vars} loc defaults depth trying env ((p, pty) :: rest) ty defining
    = try (do gam <- get Ctxt
              findPos gam p id (nf gam env pty) (nf gam env ty))
          (searchLocalWith loc defaults depth trying env rest ty defining)
  where
    findDirect : Defs -> Term vars -> 
                 (Term vars -> Term vars) ->
                 NF vars -> NF vars -> Core annot (Term vars)
    findDirect gam prf f nty ty
        = do (args, appTy) <- mkArgs loc env nty
             [] <- unify InTerm loc env ty appTy
                 | throw (CantSolveGoal loc env (quote gam env ty))
             let candidate = TT.apply (f prf) (map snd args)
             log 1 $ "Success for " ++ show (quote gam env ty) ++
                     " with " ++ show candidate ++
                     " " ++ show (quote gam env appTy)
             traverse (searchIfHole loc defaults depth trying defining) (map fst args)
             pure candidate
             
    findPos : Defs -> Term vars -> 
              (Term vars -> Term vars) ->
              NF vars -> NF vars -> Core annot (Term vars)
    findPos gam prf f x@(NTCon pn _ _ [xty, yty]) ty
        = try (findDirect gam prf f x ty)
              (do fname <- maybe (throw (CantSolveGoal loc env (quote gam env ty)))
                                 pure
                                 (fstName gam)
                  sname <- maybe (throw (CantSolveGoal loc env (quote gam env ty)))
                                 pure
                                 (sndName gam)
                  if isPairType pn gam
                     then
                       try (findPos gam prf
                               (\r => apply (Ref Bound sname)
                                            [quote gam env xty, 
                                             quote gam env yty, (f r)])
                               (evalClosure gam yty) ty)
                           (findPos gam prf
                               (\r => apply (Ref Bound fname)
                                            [quote gam env xty, 
                                             quote gam env yty, (f r)])
                               (evalClosure gam xty) ty)
                     else throw (CantSolveGoal loc env (quote gam env ty)))
    findPos gam prf f nty ty = findDirect gam prf f nty ty

searchLocal : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState annot)} ->
          annot -> Bool -> Nat -> List ClosedTerm ->
          Env Term vars -> Term vars -> Name -> Core annot (Term vars)
searchLocal loc defaults depth trying env ty defining 
    = searchLocalWith loc defaults depth trying env (getAllEnv [] env) ty defining


-- Fail with the given error if any of the determining arguments contain holes
concreteDets : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState annot)} ->
               annot -> Env Term vars -> NF vars -> Nat -> List Nat -> 
               List (Closure vars) -> Core annot ()
concreteDets loc env ty i ds [] = pure ()
concreteDets {vars} loc env ty i ds (cl :: cs)
    = if not (i `elem` ds) 
         then concreteDets loc env ty (1 + i) ds cs
         else do concrete True cl
                 concreteDets loc env ty (1 + i) ds cs
  where
    mutual
      concreteNF : Bool -> NF vars -> Core annot ()
      concreteNF top (NBind x b sc)
          = concreteNF False (sc (toClosure False env Erased))
      concreteNF top (NApp (NRef _ hn) args)
          = do gam <- get Ctxt
               hole <- nameIsHole loc hn
               if hole
                  then if top
                          then throw (DeterminingArg loc hn env (quote gam env ty)) 
                          else throw (CantSolveGoal loc env (quote gam env ty)) 
                  else do traverse (concrete False) args
                          pure ()
      concreteNF top (NApp _ args) 
          = do traverse (concrete False) args; pure ()
      concreteNF top (NDCon _ _ _ args) 
          = do traverse (concrete False) args; pure ()
      concreteNF top (NTCon _ _ _ args) 
          = do traverse (concrete False) args; pure ()
      concreteNF _ _ = pure ()

      concrete : Bool -> Closure vars -> Core annot ()
      concrete top c 
          = do defs <- get Ctxt
               concreteNF top (evalClosure defs c)

checkConcreteDets : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST (UState annot)} ->
                    annot -> Bool -> NF [] -> NF [] -> Core annot ()
-- Look inside pairs first
checkConcreteDets loc defaults ty (NTCon pn t ar [xty, yty])
    = do defs <- get Ctxt
         if isPairType pn defs
            then do checkConcreteDets loc defaults ty (evalClosure defs xty)
                    checkConcreteDets loc defaults ty (evalClosure defs yty)
            else do sd <- getSearchData loc (not defaults) pn
                    concreteDets loc [] ty 0 (detArgs sd) [xty, yty]
checkConcreteDets loc defaults ty (NTCon n t ar args)
    = do sd <- getSearchData loc (not defaults) n
         concreteDets loc [] ty 0 (detArgs sd) args
checkConcreteDets loc defaults ty (NBind n (Pi _ _ _) scfn)
    = checkConcreteDets loc defaults ty (scfn (toClosure False [] Erased))
checkConcreteDets _ _ _ _ = pure ()

-- Type directed search - take the first thing of the given type it finds using
-- the current environment.
searchType : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Bool -> Nat -> List ClosedTerm -> Env Term vars -> Name ->
             NF vars -> Core annot (Term vars)
searchType loc defaults depth trying env defining (NBind n (Pi c info ty) scfn)
    = do xn <- genName "x"
         gam <- get Ctxt
         let env' : Env Term (n :: _) = Pi c info (quote (noGam gam) env ty) :: env
         let sc = scfn (toClosure False env (Ref Bound xn))
         let tmsc = refToLocal xn n (quote (noGam gam) env sc)
         log 6 $ "Introduced lambda, search for " ++ show (normalise gam env' tmsc)
         scVal <- searchType loc defaults depth trying env' defining (nf gam env' tmsc)
         pure (Bind n (Lam c info (quote (noGam gam) env ty)) scVal)
searchType loc defaults depth trying env defining ty@(NTCon n t ar args)
    = do gam <- get Ctxt
         if length args == ar
           then do sd <- getSearchData loc (not defaults) n
                   let (dets, allOpens, allCons, chasers) =
                          (detArgs sd, globalHints sd, directHints sd, indirectHints sd)
                   let opens = filter (/=defining) allOpens
                   let cons = filter (/=defining) allCons
                   log 5 $ "Hints for " ++ show n ++ " " ++ show defaults ++ " : " ++ show cons
                   -- Solutions is either:
                   -- One of the locals
                   -- or *Exactly one* of the open hints
                   -- or, only if there are no open hints,
                   --     *Exactly one* of the other hints
                   -- or, finally, try chasing indirect hints
                   try (searchLocal loc defaults depth trying env (quote (noGam gam) env ty) defining)
                       (handleError 
                         (handleError 
                           (searchNames loc defaults depth trying env ty defining opens)
                           (\err => if ambig err
                                       then throw err
                                       else searchNames loc defaults depth trying env ty defining cons))
                           (\err => if ambig err
                                       then throw err
                                       else searchNames loc defaults depth trying env ty defining chasers))
           else throw (CantSolveGoal loc env (quote gam env ty))
  where
    ambig : Error annot -> Bool
    ambig (AmbiguousSearch _ _) = True
    ambig _ = False
searchType loc defaults depth trying env defining (NPrimVal IntType)
    = pure (PrimVal (I 0))
searchType loc defaults depth trying env defining ty 
    = do gam <- get Ctxt
         try (searchLocal loc defaults depth trying env (quote (noGam gam) env ty) defining)
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
             annot -> Bool -> Nat -> List ClosedTerm ->
             Name -> Name -> Defs -> GlobalDef -> Core annot ClosedTerm
searchHole loc defaults depth trying defining n gam glob
    = do let searchty = normaliseHoles gam [] (type glob)
         abandonIfCycle searchty trying
         let nty = nf gam [] searchty
         log 2 $ "Running search: " ++ show n ++ " in " ++ show defining ++
                 " for " ++ show (quote gam [] nty)
         dumpConstraints 5 True
         checkConcreteDets loc defaults nty nty
         soln <- searchType loc defaults depth (searchty :: trying) [] defining nty
         log 5 $ "Solution: " ++ show n ++ " = " ++ show (normalise gam [] soln)
         addDef n (record { definition = PMDef True [] (STerm soln) (STerm soln) } glob)
         removeHoleName n
         pure soln

-- Declared in Unify.idr (please remember to keep this type up to date!)
-- search : {auto c : Ref Ctxt Defs} ->
--          {auto u : Ref UST (UState annot)} ->
--          annot -> (defaults : Bool) ->
--          Nat -> List ClosedTerm -> Name -> Name -> Core annot ClosedTerm
Core.Unify.search loc defaults depth trying defining n_in
    = do gam <- get Ctxt
         case lookupHoleName n_in (gamma gam) of
              Just (n, glob) =>
                   -- The definition should be 'BySearch' at this stage,
                   -- if it's arising from an auto implicit
                   case definition glob of
                        Hole locs False _ => searchHole loc defaults depth trying defining n gam glob
                        BySearch _ _ => searchHole loc defaults depth trying defining n gam glob
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
