module TTImp.ExprSearch

-- Expression search for interactive editing. There's a lot of similarities
-- with Core.AutoSearch but I think it's better for them to be entirely
-- separate: AutoSearch is a crucial part of the core therefore it's good for
-- it to be well defined and cleanly separated from everything else, whereas
-- this search mechanism is about finding plausible candidates for programs.

-- We try to find as many results as possible, within the given search
-- depth.

import Core.Context
import Core.TT
import Core.CaseTree
import Core.Normalise
import Core.Unify

import Data.List

%default covering

search : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST (UState annot)} ->
         annot -> 
         Nat -> List ClosedTerm -> Name -> 
         Maybe ClosedTerm ->
         Name -> Core annot (List ClosedTerm)

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
               annot -> Nat -> List ClosedTerm ->
               Name -> Maybe ClosedTerm -> Env Term vars -> (Name, Term vars) -> 
               Core annot (List (Term vars))
searchIfHole loc Z trying defining topty env n 
    = pure []
searchIfHole loc (S depth) trying defining topty env (n, napp)
    = if !(nameIsHole loc n) 
         then do gam <- get Ctxt
                 tms <- search loc depth trying defining topty n
                 pure (map (\tm => normaliseHoles gam env 
                                         (applyTo (embed tm) env)) tms)
         else pure [napp]

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

mkCandidates : Term vars -> List (List (Term vars)) -> List (Term vars)
mkCandidates f [] = pure f
mkCandidates f (args :: argss)
    = do arg <- args
         mkCandidates (App f arg) argss

-- Apply the name to arguments and see if the result unifies with the target
-- type, then try to automatically solve any holes which were generated.
-- If there are any remaining holes, search fails.
searchName : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Nat -> List ClosedTerm ->
             Env Term vars -> NF vars -> Maybe ClosedTerm ->
             Name -> (Name, GlobalDef) -> Core annot (List (Term vars))
searchName loc depth trying env ty topty defining (con, condef)
    = do gam <- get Ctxt
         let cty = type condef
         log 5 $ "Trying " ++ show con
         case definition condef of
              DCon tag arity _
                  => do let nty = nf gam env (embed cty)
                        (args, appTy) <- mkArgs loc env nty
                        log 10 $ "Unifying " ++ show (quote gam env ty) ++
                                   " and " ++
                                   show (quote gam env appTy)
                        [] <- unify InTerm loc env ty appTy
                              | _ => pure []
                        gam <- get Ctxt
                        args' <- traverse (searchIfHole loc depth trying defining topty env) 
                                          args
                        let cs = mkCandidates (Ref (DataCon tag arity) con) args'
                        log 10 $ "Candidates for " ++ show con ++ " " ++ show cs
                                ++ " from " ++ show args'
                        pure cs
              _ => do let nty = nf gam env (embed cty)
                      ctxt <- get Ctxt
                      (args, appTy) <- mkArgs loc env nty
                      log 10 $ "Unifying " ++ show (quote gam env ty) ++
                                   " and " ++
                                   show (quote gam env appTy)
                      [] <- unify InTerm loc env ty appTy
                            | _ => pure []
                      let candidate = apply (Ref Func con) (map snd args)
                      -- Go through the arguments and solve them, if they
                      -- haven't been solved by unification
                      args' <- traverse (searchIfHole loc depth trying defining topty env) 
                                        args
                      let cs = mkCandidates (Ref Func con) args'
                      log 10 $ "Candidates for " ++ show con ++ " " ++ show cs
                                ++ " from " ++ show args'
                      pure cs

successful : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             List (Core annot a) ->
             Core annot (List (Either (Error annot) a))
successful [] = pure []
successful (elab :: elabs)
-- Don't save any state, we'll happily keep adding variables and unification
-- problems because we might be creating multiple candidate solutions, and
-- they won't interfere.
-- We will go back to the original state once we're done!
    = catch (do res <- elab
                rest <- successful elabs
                pure (Right res :: rest))
            (\err => 
                do rest <- successful elabs
                   pure (Left err :: rest))

getSuccessful : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState annot)} ->
                annot -> Bool ->
                Env Term vars -> Term vars -> Maybe ClosedTerm ->
                List (Core annot (List (Term vars))) ->
                Core annot (List (Term vars))
getSuccessful loc mkHole env ty topty all
    = do elabs <- successful all
         case concat (rights elabs) of
              [] => -- If no successful search, make a hole
                if mkHole
                   then do defs <- get Ctxt
                           n <- addHole loc env ty "search"
                           log 10 $ "All failed, added hole for " ++
                                     show ty ++ " (" ++ show n ++ ")"
                           pure [mkConstantApp n env]
                   else pure []
              rs => pure rs

searchNames : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              annot -> Nat -> List ClosedTerm -> Env Term vars ->
              Term vars -> Maybe ClosedTerm ->
              Name -> List Name -> Core annot (List (Term vars))
searchNames loc depth trying env ty topty defining []
    = pure []
searchNames loc depth trying env ty topty defining (n :: ns)
    = do gam <- get Ctxt
         let visns = mapMaybe (visible (gamma gam) (currentNS gam)) (n :: ns)
         log 5 $ "Searching " ++ show (map fst visns) ++ " for " ++ show ty
         let nfty = nf gam env ty
         getSuccessful loc False env ty topty
            (map (searchName loc depth trying env nfty topty defining) visns)
  where
    visible : Gamma -> List String -> Name -> Maybe (Name, GlobalDef)
    visible gam nspace n
        = do def <- lookupGlobalExact n gam
             if visibleIn nspace n (visibility def)
                then Just (n, def)
                else Nothing

-- A local is usable if it contains no holes in an argument position
usableLocal : {auto c : Ref Ctxt Defs} ->
              annot -> Env Term vars -> NF vars -> Core annot Bool
usableLocal loc env (NApp (NRef _ n) args)
    = do u <- nameIsHole loc n
         if not u
            then do defs <- get Ctxt
                    us <- traverse (usableLocal loc env) 
                                   (map (evalClosure defs) args)
                    pure (and (map Delay us))
            else pure False
usableLocal {vars} loc env (NTCon n _ _ args)
    = do defs <- get Ctxt
         us <- traverse (usableLocal loc env) 
                        (map (evalClosure defs) args)
         pure (and (map Delay us))
usableLocal loc env (NDCon n _ _ args)
    = do defs <- get Ctxt
         us <- traverse (usableLocal loc env) 
                        (map (evalClosure defs) args)
         pure (and (map Delay us))
usableLocal loc env (NApp (NLocal _ _) args)
    = do defs <- get Ctxt
         us <- traverse (usableLocal loc env) 
                        (map (evalClosure defs) args)
         pure (and (map Delay us))
usableLocal loc env (NBind x (Pi _ _ _) sc)
    = usableLocal loc env (sc (toClosure defaultOpts env Erased))
usableLocal loc _ _ = pure True

searchLocalWith : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST (UState annot)} ->
                  annot -> Nat -> List ClosedTerm ->
                  Env Term vars -> List (Term vars, Term vars) ->
                  Term vars -> Maybe ClosedTerm -> Name -> Core annot (List (Term vars))
searchLocalWith loc depth trying env [] ty topty defining
    = pure []
searchLocalWith {vars} loc depth trying env ((p, pty) :: rest) ty topty defining
    = do gam <- get Ctxt
         getSuccessful loc False env ty topty
                       [findPos gam p id (nf gam env pty) ty,
                        searchLocalWith loc depth trying env rest ty
                                        topty defining]
  where
    findDirect : Defs -> Term vars -> 
                 (Term vars -> Term vars) ->
                 NF vars -> -- local variable's type
                 NF vars -> -- type we're looking for
                 Core annot (List (Term vars))
    findDirect gam prf f nty ty
        = do (args, appTy) <- mkArgs loc env nty
             -- We can only use a local variable if it's not an unsolved
             -- hole
             u <- usableLocal loc env nty
             if u
                then do
                  [] <- unify InTerm loc env ty appTy
                     | _ => pure []
                  args' <- traverse (searchIfHole loc depth trying defining topty env) 
                                    args
                  pure (mkCandidates (f prf) args')
                else pure []

    findPos : Defs -> Term vars -> 
              (Term vars -> Term vars) ->
              NF vars -> Term vars -> Core annot (List (Term vars))
    findPos gam prf f x@(NTCon pn _ _ [xty, yty]) ty
        = getSuccessful loc False env ty topty
              [findDirect gam prf f x (nf gam env ty),
                 (do fname <- maybe (cantSolve loc env (quote gam env ty) topty)
                                    pure
                                    (fstName gam)
                     sname <- maybe (cantSolve loc env (quote gam env ty) topty)
                                    pure
                                    (sndName gam)
                     if isPairType pn gam
                        then getSuccessful loc False env ty topty
                               [findPos gam prf
                                   (\r => apply (Ref Bound sname)
                                                [quote gam env xty, 
                                                 quote gam env yty, (f r)])
                                   (evalClosure gam yty) ty,
                                findPos gam prf
                                   (\r => apply (Ref Bound fname)
                                                [quote gam env xty, 
                                                 quote gam env yty, (f r)])
                                   (evalClosure gam xty) ty]
                         else pure [])]
    findPos gam prf f nty ty = findDirect gam prf f nty (nf gam env ty)

searchLocal : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              annot -> Nat -> List ClosedTerm ->
              Env Term vars -> Term vars -> Maybe ClosedTerm ->
              Name -> Core annot (List (Term vars))
searchLocal loc depth trying env ty topty defining 
    = do defs <- get Ctxt
         searchLocalWith loc depth trying env (getAllEnv [] env) 
                         ty topty defining

searchType : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Nat -> List ClosedTerm -> Env Term vars -> Name ->
             Maybe ClosedTerm ->
             Term vars -> Core annot (List (Term vars))
searchType loc depth trying env defining topty (Bind n (Pi c info ty) sc)
    = do let env' : Env Term (n :: _) = Pi c info ty :: env
         log 6 $ "Introduced lambda, search for " ++ show sc
         scVal <- searchType loc depth trying env' defining topty sc
         pure (map (Bind n (Lam c info ty)) scVal)
searchType loc depth trying env defining topty ty
    = case getFnArgs ty of
           (Ref (TyCon t ar) n, args) =>
                do gam <- get Ctxt
                   if length args == ar
                     then do sd <- getSearchData loc True n
                             let (dets, allOpens, allCons, chasers) =
                                    (detArgs sd, globalHints sd, directHints sd, indirectHints sd)
                             let opens = filter (/=defining) allOpens
                             let cons = filter (/=defining) allCons
                             log 5 $ "Hints for " ++ show n ++ " : " ++ show cons
                             -- Solutions is either:
                             -- First try the locals,
                             -- Then try the hints in order
                             getSuccessful loc True env ty topty
                                  [searchLocal loc depth trying env ty topty defining,
                                   searchNames loc depth trying env ty topty defining
                                               (opens ++ cons ++ chasers)]
                     else pure []
           _ => do log 5 $ "Searching locals only at " ++ show ty
                   getSuccessful loc True env ty topty
                       [searchLocal loc depth trying env ty topty defining]
  where
    ambig : Error annot -> Bool
    ambig (AmbiguousSearch _ _ _) = True
    ambig _ = False

-- No need to normalise the binders - this is the slow part of normalisation
-- in any case when we recalculate their de Bruijn index, so if we can avoid
-- it, it's a big win
normaliseScope : Defs -> Env Term vars -> Term vars -> Term vars
normaliseScope defs env (Bind n b sc) 
    = Bind n b (normaliseScope defs (b :: env) sc)
normaliseScope defs env tm = normaliseHoles defs env tm

searchHole : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Nat -> List ClosedTerm ->
             Name -> Name -> 
             Maybe ClosedTerm ->
             Defs -> GlobalDef -> Core annot (List ClosedTerm)
searchHole loc depth trying defining n topty gam glob
    = do let searchty = normaliseScope gam [] (type glob)
         log 5 $ "Running search: " ++ show n ++ " in " ++ show defining ++
                 " for " ++ show searchty
         dumpConstraints 5 True
         searchType loc depth (searchty :: trying) [] defining topty searchty

-- Declared at the top
search loc depth trying defining topty n_in
    = do gam <- get Ctxt
         case lookupHoleName n_in (gamma gam) of
              Just (n, glob) =>
                   -- The definition should be 'BySearch' at this stage,
                   -- if it's arising from an auto implicit
                   case definition glob of
                        Hole locs False _ => searchHole loc depth trying defining n topty gam glob
                        BySearch _ _ => searchHole loc depth trying defining n topty gam glob
                        _ => do log 10 $ show n_in ++ " not a hole"
                                throw (InternalError $ "Not a hole: " ++ show n ++ " in " ++ show defining)
              _ => do log 10 $ show n_in ++ " not found"
                      throw (UndefinedName loc n_in)
  where
    lookupHoleName : Name -> Gamma -> Maybe (Name, GlobalDef)
    lookupHoleName n gam
        = case lookupGlobalExact n gam of
               Just res => Just (n, res)
               Nothing => case lookupGlobalName n gam of
                               [res] => Just res
                               _ => Nothing

export
exprSearch : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Name -> List Name -> Core annot (List ClosedTerm)
exprSearch loc n hints
    = search loc 10 [] (UN "(search)") Nothing n

