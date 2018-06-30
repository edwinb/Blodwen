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
-- If the type of the variable at the top of the environment (or any of its
-- fields if it's a tuple) converts with the goal, use it 
-- (converts, not unifying, so no solving metavariables here)
    = try (do gam <- get Ctxt
              let bty = binderType b
              case findPos gam (b :: env) id
                           (nf gam (b :: env) (weaken bty)) 
                           (nf gam (b :: env) ty) of
                   Just res => do log 6 $ "Trivial success: " ++ show v ++ " : " ++ show (weaken {n = v} bty)
                                     ++ " for " ++ show ty
                                  pure res
                   Nothing => do log 7 $ "Trivial fail: " ++ show v ++ " : " ++ show (weaken {n = v} bty)
                                     ++ " for " ++ show ty
                                 throw (CantSolveGoal loc (b :: env) ty))
          (case shrinkTerm ty (DropCons SubRefl) of
                Nothing => throw (CantSolveGoal loc (b :: env) ty)
                Just ty' => do tm' <- trivial loc env ty'
                               pure (weaken tm'))
  where
    findPos : Defs -> Env Term (v :: vs) -> 
              (Term (v :: vs) -> Term (v :: vs)) ->
              NF (v :: vs) -> NF (v :: vs) -> 
              Maybe (Term (v :: vs))
    findPos gam env f x@(NTCon pn _ _ [xty, yty]) ty
        = if convert gam env x ty
             then Just (f (Local Here))
             else
               do fname <- fstName gam
                  sname <- sndName gam
                  if isPairType pn gam
                     then maybe
                      (findPos gam env 
                               (\r => apply (Ref Bound sname)
                                            [Erased, Erased, (f r)])
                               (evalClosure gam yty) ty)
                      Just 
                      (findPos gam env 
                               (\r => apply (Ref Bound fname)
                                            [Erased, Erased, (f r)])
                               (evalClosure gam xty) ty)
                     else Nothing
    findPos gam env f x ty
        = if convert gam env x ty
             then Just (f (Local Here))
             else Nothing

mkArgs : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST (UState annot)} ->
         annot -> Env Term vars -> Term vars -> 
         Core annot (List (Name, Term vars), Term vars)
mkArgs loc env (Bind n (Pi c info ty) sc)
    = do argName <- genName "sa"
         addNamedHole loc argName False env ty
         let arg = mkConstantApp argName env
         (rest, restTy) <- mkArgs loc env (subst arg sc)
         pure ((argName, arg) :: rest, restTy)
mkArgs loc env ty = pure ([], ty)

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
                        -- Go through the arguments and solve them, if they
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
                        -- Go through the arguments and solve them, if they
                        -- haven't been solved by unification
                        traverse (searchIfHole loc depth trying defining) (map fst args)
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
              annot -> Nat -> List ClosedTerm -> Env Term vars -> NF vars -> 
              Name -> List Name -> Core annot (Term vars)
searchNames loc depth trying env ty defining []
    = do gam <- get Ctxt
         throw (CantSolveGoal loc env (quote gam env ty))
searchNames loc depth trying env ty defining (n :: ns)
    = do gam <- get Ctxt
         log 5 $ "Searching " ++ show (n :: ns) ++ " for " ++ show (quote gam env ty)
         exactlyOne loc env ty 
            (map (searchName loc depth trying env ty defining) (n :: ns))

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
           then do (dets, allOpens, allCons) <- getSearchData loc n
                   let opens = filter (/=defining) allOpens
                   let cons = filter (/=defining) allCons
                   concreteDets loc env ty 0 dets args
                   log 5 $ "Hints for " ++ show n ++ ": " ++ show cons
                   -- Solutions is either:
                   -- One of the locals
                   -- or *Exactly one* of the open hints
                   -- or, only if there are no open hints,
                   --     *Exactly one* of the other hints
                   try (trivial loc env (quote (noGam gam) env ty))
                       (handleError 
                         (searchNames loc depth trying env ty defining opens)
                         (\err => if ambig err
                                     then throw err
                                     else searchNames loc depth trying env ty defining cons))
           else throw (CantSolveGoal loc env (quote gam env ty))
  where
    ambig : Error annot -> Bool
    ambig (AmbiguousSearch _ _) = True
    ambig _ = False
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
         dumpConstraints 5 True
         soln <- searchType loc depth (searchty :: trying) [] defining nty
         log 5 $ "Solution: " ++ show n ++ " = " ++ show (normalise gam [] soln)
         addDef n (record { definition = PMDef True [] (STerm soln) } glob)
         removeHoleName n
         pure soln

-- Declared in Unify.idr (please remember to keep this type up to date!)
-- search : {auto c : Ref Ctxt Defs} ->
--          {auto u : Ref UST (UState annot)} ->
--          annot -> Nat -> List ClosedTerm -> Name -> Name -> Core annot ClosedTerm
Core.Unify.search loc depth trying defining n_in
    = do gam <- get Ctxt
         case lookupHoleName n_in (gamma gam) of
              Just (n, glob) =>
                   -- The definition should be 'BySearch' at this stage,
                   -- if it's arising from an auto implicit
                   case definition glob of
                        Hole locs False _ => searchHole loc depth trying defining n gam glob
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
