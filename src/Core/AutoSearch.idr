module Core.AutoSearch

-- Proof search for auto implicits and interface implementations

import Core.Context
import Core.TT
import Core.CaseTree
import Core.Normalise
import Core.Unify

import Data.List

%default covering

mkArgs : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST (UState annot)} ->
         annot -> Env Term vars -> NF vars -> 
         Core annot (List (Name, Term vars), NF vars)
mkArgs loc env (NBind n (Pi c info ty) sc)
    = do gam <- get Ctxt
         argName <- genName "sa"
         addNamedHole loc argName False env (quote (noGam gam) env ty)
         setInvertible loc argName
         let arg = mkConstantApp argName env
         (rest, restTy) <- mkArgs loc env (sc (MkClosure defaultOpts [] env arg))
         pure ((argName, arg) :: rest, restTy)
mkArgs loc env ty = pure ([], ty)

getAllEnv : (done : List Name) -> 
            Env Term vars -> List (Term (done ++ vars), Term (done ++ vars))
getAllEnv done [] = []
getAllEnv {vars = v :: vs} done (b :: env) 
   = let rest = getAllEnv (done ++ [v]) env in
         (Local Nothing (weakenElem {ns = done} Here), 
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
               annot -> Bool -> Bool -> Nat -> List ClosedTerm ->
               Name -> Maybe ClosedTerm -> Name -> Core annot ()
searchIfHole loc defaults updatety Z trying defining topty n 
    = throw (InternalError "Search depth limit reached")
searchIfHole loc defaults updatety (S depth) trying defining topty n
    = if !(nameIsHole loc n) 
         then do gam <- get Ctxt
                 let topty' 
                    = if updatety 
                         then case lookupTyExact n (gamma gam) of
                                   Nothing => topty
                                   Just t' => Just (normalise gam [] t')
                         else topty
                 search loc defaults depth trying defining topty' n
                 pure ()
         else pure ()

cantSolve : {auto c : Ref Ctxt Defs} ->
            annot -> Env Term vars -> Term vars -> Maybe ClosedTerm ->
            Core annot a
cantSolve loc env thisty Nothing = throw (CantSolveGoal loc (bindEnv env thisty))
cantSolve loc env thisty (Just topty) 
   = do gam <- get Ctxt
        throw (CantSolveGoal loc (embed topty))

isPairNF : Env Term vars -> NF vars -> Defs -> Bool
isPairNF env (NTCon n _ _ _) defs
    = isPairType n defs
isPairNF env (NBind b (Pi _ _ _) sc) defs
    = isPairNF env (sc (toClosure defaultOpts env Erased)) defs
isPairNF _ _ _ = False

-- Apply the name to arguments and see if the result unifies with the target
-- type, then try to automatically solve any holes which were generated.
-- If there are any remaining holes, search fails.
searchName : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Bool -> Nat -> List ClosedTerm ->
             Env Term vars -> NF vars -> Maybe ClosedTerm ->
             Name -> (Name, GlobalDef) -> Core annot (Term vars)
searchName loc defaults depth trying env ty topty defining (con, condef)
    = do gam <- get Ctxt
         let cty = type condef
         case definition condef of
              DCon tag arity _
                  => do let nty = nf gam env (embed cty)
                        (args, appTy) <- mkArgs loc env nty
                        [] <- unify InTerm loc env ty appTy
                              | _ => cantSolve loc env (quote gam env ty) topty
                        let candidate = apply (Ref (DataCon tag arity) con)
                                              (map snd args)
                        gam <- get Ctxt
                        -- if it's a pair, we'll update the reported top type
                        -- for the sake of error messages, so check here
                        let ispair = isPairNF env nty gam
                        -- Go through the arguments and solve them, if they
                        -- haven't been solved by unification
                        traverse (searchIfHole loc defaults ispair 
                                               depth trying defining topty) 
                                 (map fst args)
                        pure candidate
              _ => do let nty = nf gam env (embed cty)
                      ctxt <- get Ctxt
                      (args, appTy) <- mkArgs loc env nty
                      [] <- unify InTerm loc env ty appTy
                            | _ => cantSolve loc env (quote gam env ty) topty
                      let candidate = apply (Ref Func con) (map snd args)
                      -- Go through the arguments and solve them, if they
                      -- haven't been solved by unification
                      traverse (searchIfHole loc defaults False 
                                             depth trying defining topty) 
                               (map fst args)
                      pure candidate

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
             annot -> Env Term vars -> Term vars -> Maybe ClosedTerm -> 
             List (Core annot (Term vars)) ->
             Core annot (Term vars)
exactlyOne loc env ty topty [elab] 
    = catch elab
         (\err => case err of
                       CantSolveGoal _ _ => throw err
                       _ => cantSolve loc env ty topty)
exactlyOne loc env ty topty all
    = do elabs <- successful all
         case rights elabs of
              [(res, state, ust)] => do put Ctxt state
                                        put UST ust
                                        pure res
              [] => do gam <- get Ctxt
                       cantSolve loc env ty topty
              rs => throw (AmbiguousSearch loc env (map fst rs))

anyOne : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST (UState annot)} ->
         annot -> Env Term vars -> NF vars -> Maybe ClosedTerm ->
         List (Core annot (Term vars)) ->
         Core annot (Term vars)
anyOne loc env ty topty [] 
    = do gam <- get Ctxt
         cantSolve loc env (quote gam env ty) topty
anyOne loc env ty topty [elab] = elab
anyOne loc env ty topty (e :: es) = tryUnify e (anyOne loc env ty topty es)

searchNames : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              annot -> Bool -> Nat -> List ClosedTerm -> Env Term vars ->
              Term vars -> Maybe ClosedTerm ->
              Name -> List Name -> Core annot (Term vars)
searchNames loc defaults depth trying env ty topty defining []
    = do gam <- get Ctxt
         cantSolve loc env ty topty
searchNames loc defaults depth trying env ty topty defining (n :: ns)
    = do gam <- get Ctxt
         let visns = mapMaybe (visible (gamma gam) (currentNS gam)) (n :: ns)
         log 5 $ "Searching " ++ show (map fst visns) ++ " for " ++ show ty
         let nfty = nf gam env ty
         exactlyOne loc env ty topty
            (map (searchName loc defaults depth trying env nfty topty defining) visns)
  where
    visible : Gamma -> List String -> Name -> Maybe (Name, GlobalDef)
    visible gam nspace n
        = do def <- lookupGlobalExact n gam
             if visibleIn nspace n (visibility def)
                then Just (n, def)
                else Nothing

-- A local is usable if it contains no holes in a determining argument position
usableLocal : {auto c : Ref Ctxt Defs} ->
              annot -> Bool -> Env Term vars -> NF vars -> Core annot Bool
usableLocal loc defaults env (NApp (NRef _ n) args)
    = do u <- nameIsHole loc n
         if not u
            then do defs <- get Ctxt
                    us <- traverse (usableLocal loc defaults env) 
                                   (map (evalClosure defs) args)
                    pure (and (map Delay us))
            else pure False
usableLocal {vars} loc defaults env (NTCon n _ _ args)
    = do sd <- getSearchData loc (not defaults) n
         usableLocalArg 0 (detArgs sd) args
  -- usable if none of the determining arguments of the local's type are
  -- holes
  where
    usableLocalArg : Nat -> List Nat -> List (Closure vars) -> Core annot Bool
    usableLocalArg i dets [] = pure True
    usableLocalArg i dets (c :: cs)
        = if i `elem` dets
             then do defs <- get Ctxt
                     u <- usableLocal loc defaults env (evalClosure defs c) 
                     if u
                        then usableLocalArg (1 + i) dets cs
                        else pure False
             else usableLocalArg (1 + i) dets cs
usableLocal loc defaults env (NDCon n _ _ args)
    = do defs <- get Ctxt
         us <- traverse (usableLocal loc defaults env) 
                        (map (evalClosure defs) args)
         pure (and (map Delay us))
usableLocal loc defaults env (NApp (NLocal _ _) args)
    = do defs <- get Ctxt
         us <- traverse (usableLocal loc defaults env) 
                        (map (evalClosure defs) args)
         pure (and (map Delay us))
usableLocal loc defaults env (NBind x (Pi _ _ _) sc)
    = usableLocal loc defaults env (sc (toClosure defaultOpts env Erased))
usableLocal loc _ _ _ = pure True

searchLocalWith : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST (UState annot)} ->
                  annot -> Bool -> Nat -> List ClosedTerm ->
                  Env Term vars -> List (Term vars, Term vars) ->
                  NF vars -> Maybe ClosedTerm -> Name -> Core annot (Term vars)
searchLocalWith loc defaults depth trying env [] ty topty defining
    = do defs <- get Ctxt
         cantSolve loc env (quote defs env ty) topty
searchLocalWith {vars} loc defaults depth trying env ((p, pty) :: rest) ty topty defining
    = tryUnify
          (do gam <- get Ctxt
              findPos gam p id (nf gam env pty) ty)
          (searchLocalWith loc defaults depth trying env rest ty topty defining)
  where
    findDirect : Defs -> Term vars -> 
                 (Term vars -> Term vars) ->
                 NF vars -> -- local variable's type
                 NF vars -> -- type we're looking for
                 Core annot (Term vars)
    findDirect gam prf f nty ty
        = do (args, appTy) <- mkArgs loc env nty
             -- We can only use a local variable if it's not an unsolved
             -- hole
             u <- usableLocal loc defaults env nty
             if u
                then do
                  [] <- unify InTerm loc env ty appTy
                     | _ => cantSolve loc env (quote gam env ty) topty
                  let candidate = TT.apply (f prf) (map snd args)
                  log 1 $ "Success for " ++ show (quote gam env ty) ++
                          " with " ++ show (normalise gam env candidate) ++
                          " " ++ show (quote gam env appTy)
                  traverse (searchIfHole loc defaults False 
                                         depth trying defining topty) 
                           (map fst args)
                  pure candidate
                else cantSolve loc env (quote gam env ty) topty
             
    findPos : Defs -> Term vars -> 
              (Term vars -> Term vars) ->
              NF vars -> NF vars -> Core annot (Term vars)
    findPos gam prf f x@(NTCon pn _ _ [xty, yty]) ty
        = tryUnify (findDirect gam prf f x ty)
              (do fname <- maybe (cantSolve loc env (quote gam env ty) topty)
                                 pure
                                 (fstName gam)
                  sname <- maybe (cantSolve loc env (quote gam env ty) topty)
                                 pure
                                 (sndName gam)
                  if isPairType pn gam
                     then
                       tryUnify
                           (findPos gam prf
                               (\r => apply (Ref Bound sname)
                                            [quote gam env xty, 
                                             quote gam env yty, (f r)])
                               (evalClosure gam yty) ty)
                           (findPos gam prf
                               (\r => apply (Ref Bound fname)
                                            [quote gam env xty, 
                                             quote gam env yty, (f r)])
                               (evalClosure gam xty) ty)
                     else cantSolve loc env (quote gam env ty) topty)
    findPos gam prf f nty ty = findDirect gam prf f nty ty

searchLocal : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState annot)} ->
          annot -> Bool -> Nat -> List ClosedTerm ->
          Env Term vars -> Term vars -> Maybe ClosedTerm ->
          Name -> Core annot (Term vars)
searchLocal loc defaults depth trying env ty topty defining 
    = do defs <- get Ctxt
         searchLocalWith loc defaults depth trying env (getAllEnv [] env) 
                         (nf defs env ty) topty defining


-- Fail with the given error if any of the determining arguments contain holes
concreteDets : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState annot)} ->
               annot -> Term [] -> Nat -> List Nat -> Maybe ClosedTerm ->
               List (Term vars) -> Core annot ()
concreteDets loc ty i ds topty [] = pure ()
concreteDets {vars} loc ty i ds topty (cl :: cs)
    = if not (i `elem` ds) 
         then concreteDets loc ty (1 + i) ds topty cs
         else do concrete True cl
                 concreteDets loc ty (1 + i) ds topty cs
  where
    mutual
      concrete : Bool -> Term vs -> Core annot ()
      concrete top (Bind x b sc)
          = concrete False sc
      concrete top tm
          = case getFnArgs tm of
                 (Ref _ hn, args) =>
                      do gam <- get Ctxt
                         hole <- nameIsHole loc hn
                         if hole
                            then if top
                                    then throw (DeterminingArg loc hn [] ty) 
                                    else cantSolve loc [] ty topty
                            else do traverse (concrete False) args
                                    pure ()
                 _ => pure ()

checkConcreteDets : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST (UState annot)} ->
                    annot -> Bool -> Term [] -> Maybe ClosedTerm ->
                    Term vars -> Core annot ()
-- Look inside pairs first
checkConcreteDets loc defaults ty topty (App (App (Ref (TyCon t ar) pn) xty) yty)
    = do defs <- get Ctxt
         if isPairType pn defs
            then do checkConcreteDets loc defaults ty topty xty
                    checkConcreteDets loc defaults ty topty yty
            else do sd <- getSearchData loc (not defaults) pn
                    concreteDets loc ty 0 (detArgs sd) topty [xty, yty]
checkConcreteDets loc defaults ty topty (Bind n (Pi c p pty) sc)
    = checkConcreteDets loc defaults ty topty sc
checkConcreteDets loc defaults ty topty tm
    = case getFnArgs tm of
           (Ref (TyCon t ar) n, args) =>
                do sd <- getSearchData loc (not defaults) n
                   concreteDets loc ty 0 (detArgs sd) topty args
           _ => pure ()

-- Type directed search - take the first thing of the given type it finds using
-- the current environment.
searchType : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Bool -> Nat -> List ClosedTerm -> Env Term vars -> Name ->
             Maybe ClosedTerm ->
             Term vars -> Core annot (Term vars)
searchType loc defaults depth trying env defining topty (Bind n (Pi c info ty) sc)
    = do let env' : Env Term (n :: _) = Pi c info ty :: env
         log 6 $ "Introduced lambda, search for " ++ show sc
         scVal <- searchType loc defaults depth trying env' defining topty sc
         pure (Bind n (Lam c info ty) scVal)
searchType loc defaults depth trying env defining topty ty
    = case getFnArgs ty of
           (Ref (TyCon t ar) n, args) =>
                do gam <- get Ctxt
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
                             tryUnify (searchLocal loc defaults depth trying env ty topty defining)
                                 (handleUnify 
                                   (handleUnify 
                                     (searchNames loc defaults depth trying env ty topty defining opens)
                                     (\err => if ambig err || (isNil cons && isNil chasers)
                                                 then throw err
                                                 else searchNames loc defaults depth trying env ty topty defining cons))
                                     (\err => if ambig err || isNil chasers
                                                 then throw err
                                                 else searchNames loc defaults depth trying env ty topty defining chasers))
                     else cantSolve loc env ty topty
           _ => do gam <- get Ctxt
                   tryUnify
                       (searchLocal loc defaults depth trying env ty topty defining)
                       (cantSolve loc env ty topty)
  where
    ambig : Error annot -> Bool
    ambig (AmbiguousSearch _ _ _) = True
    ambig _ = False

abandonIfCycle : {auto c : Ref Ctxt Defs} ->
                 ClosedTerm -> List ClosedTerm -> Core annot ()
abandonIfCycle tm [] = pure ()
abandonIfCycle tm (ty :: tys)
    = do defs <- get Ctxt
         if convert defs [] tm ty
            then throw (InternalError "Cycle in search")
            else abandonIfCycle tm tys

-- No need to normalise the binders - this is the slow part of normalisation
-- in any case when we recalculate their de Bruijn index, so if we can avoid
-- it, it's a big win
normaliseScope : Defs -> Env Term vars -> Term vars -> Term vars
normaliseScope defs env (Bind n b sc) 
    = Bind n b (normaliseScope defs (b :: env) sc)
normaliseScope defs env tm = normaliseHoles defs env tm

searchHole : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Bool -> Nat -> List ClosedTerm ->
             Name -> Name -> 
             Maybe ClosedTerm ->
             Defs -> GlobalDef -> Core annot ClosedTerm
searchHole loc defaults depth trying defining n topty gam glob
    = do let searchty = normaliseScope gam [] (type glob)
         abandonIfCycle searchty trying
         log 2 $ "Running search: " ++ show n ++ " in " ++ show defining ++
                 " for " ++ show searchty ++ " defaults " ++ show defaults
         dumpConstraints 5 True
         checkConcreteDets loc defaults searchty topty searchty
         log 5 $ "Determining arguments okay"
         soln <- searchType loc defaults depth (searchty :: trying) [] defining topty searchty
         log 5 $ "Solution: " ++ show n ++ " = " ++ show (normalise gam [] soln)
         addDef n (record { definition = PMDef True [] (STerm soln) (STerm soln) [] } glob)
         removeHoleName n
         pure soln

-- Declared in Unify.idr (please remember to keep this type up to date!)
-- search : {auto c : Ref Ctxt Defs} ->
--          {auto u : Ref UST (UState annot)} ->
--          annot -> (defaults : Bool) ->
--          Nat -> List ClosedTerm -> Name -> 
--          Maybe ClosedTerm ->
--          Name -> Core annot ClosedTerm
Core.Unify.search loc defaults depth trying defining topty n_in
    = do gam <- get Ctxt
         case lookupHoleName n_in (gamma gam) of
              Just (n, glob) =>
                   -- The definition should be 'BySearch' at this stage,
                   -- if it's arising from an auto implicit
                   case definition glob of
                        Hole locs False _ => searchHole loc defaults depth trying defining n topty gam glob
                        BySearch _ _ => searchHole loc defaults depth trying defining n topty gam glob
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
