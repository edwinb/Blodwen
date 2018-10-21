module TTImp.ExprSearch

-- Expression search for interactive editing. There's a lot of similarities
-- with Core.AutoSearch but I think it's better for them to be entirely
-- separate: AutoSearch is a crucial part of the core therefore it's good for
-- it to be well defined and cleanly separated from everything else, whereas
-- this search mechanism is about finding plausible candidates for programs.

-- We try to find as many results as possible, within the given search
-- depth.

import Core.CaseTree
import Core.Context
import Core.LinearCheck
import Core.Metadata
import Core.Normalise
import Core.Unify
import Core.TT

import TTImp.CaseSplit
import TTImp.Utils

import Data.List

%default covering

-- Data for building recursive calls - the function name, and the structure
-- of the LHS. Only recursive calls with a different structure are okay.
record RecData where
  constructor MkRecData
  recname : Name
  lhsapp : Term vars

record SearchOpts where
  constructor MkSearchOpts
  holesOK : Bool
  recOK : Bool
  depth : Nat

search : {auto c : Ref Ctxt Defs} ->
         {auto m : Ref Meta (Metadata annot)} ->
         {auto u : Ref UST (UState annot)} ->
         annot -> 
         SearchOpts -> Maybe RecData -> 
         Maybe ClosedTerm ->
         Name -> Core annot (List ClosedTerm)

mkArgs : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST (UState annot)} ->
         annot -> Env Term vars -> NF vars -> 
         Core annot (List (Name, Bool, Term vars), NF vars)
mkArgs loc env (NBind n (Pi c info ty) sc)
    = do gam <- get Ctxt
         argName <- genName "sa"
         addNamedHole loc argName False env (quote (noGam gam) env ty)
         setInvertible loc argName
         let arg = mkConstantApp argName env
         (rest, restTy) <- mkArgs loc env (sc (MkClosure defaultOpts [] env arg))
         pure ((argName, explicit info, arg) :: rest, restTy)
  where
    explicit : PiInfo -> Bool
    explicit Explicit = True
    explicit _ = False
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
             {auto m : Ref Meta (Metadata annot)} ->
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
               {auto m : Ref Meta (Metadata annot)} ->
               {auto u : Ref UST (UState annot)} ->
               annot -> SearchOpts -> Maybe RecData -> Maybe ClosedTerm -> 
               Env Term vars -> (Name, Bool, Term vars) -> 
               Core annot (List (Term vars))
searchIfHole loc opts defining topty env (n, _, napp) 
    = case depth opts of
           Z => pure []
           S k =>
              if !(nameIsHole loc n) 
                 then do gam <- get Ctxt
                         tms <- search loc (record { depth = k } opts)
                                       defining topty n
                         pure (map (\tm => normaliseHoles gam env 
                                                 (applyTo (embed tm) env)) tms)
                 else pure [napp]

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
             {auto m : Ref Meta (Metadata annot)} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> SearchOpts -> 
             Env Term vars -> NF vars -> Maybe ClosedTerm ->
             Maybe RecData -> (Name, GlobalDef) -> Core annot (List (Term vars))
searchName loc opts env ty topty defining (con, condef)
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
                        [] <- unify InSearch loc env ty appTy
                           | _ => pure []
                        gam <- get Ctxt
                        -- Search the explicit arguments first
                        args' <- traverse (searchIfHole loc opts defining topty env) 
                                          (filter (\arg => fst (snd arg)) args)
                        args' <- traverse (searchIfHole loc opts defining topty env) 
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
                      [] <- unify InSearch loc env ty appTy
                         | _ => pure []
                      -- Go through the arguments and solve them, if they
                      -- haven't been solved by unification
                      -- Search the explicit arguments first
                      args' <- traverse (searchIfHole loc opts defining topty env) 
                                        (filter (\arg => fst (snd arg)) args)
                      args' <- traverse (searchIfHole loc opts defining topty env) 
                                        args
                      let cs = mkCandidates (Ref Func con) args'
                      log 10 $ "Candidates for " ++ show con ++ " " ++ show cs
                                ++ " from " ++ show args'
                      pure cs

successful : {auto c : Ref Ctxt Defs} ->
             {auto m : Ref Meta (Metadata annot)} ->
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
                {auto m : Ref Meta (Metadata annot)} ->
                {auto u : Ref UST (UState annot)} ->
                annot -> SearchOpts -> Bool ->
                Env Term vars -> Term vars -> Maybe ClosedTerm ->
                Maybe RecData ->
                List (Core annot (List (Term vars))) ->
                Core annot (List (Term vars))
getSuccessful {vars} loc opts mkHole env ty topty defining all
    = do elabs <- successful all
         case concat (rights elabs) of
              [] => -- If no successful search, make a hole
                if mkHole && holesOK opts
                   then do defs <- get Ctxt
                           let base = maybe "arg"
                                            (\r => nameRoot (recname r) ++ "_rhs")
                                            defining
                           let hn = uniqueName defs (map nameRoot vars) base
                           n <- addHole loc env ty hn
                           log 10 $ "All failed, added hole for " ++
                                     show ty ++ " (" ++ show n ++ ")"
                           pure [mkConstantApp n env]
                   else if holesOK opts
                           then pure []
                           else throw (maybe (CantSolveGoal loc (bindEnv env ty))
                                             (\pty => CantSolveGoal loc (embed pty))
                                             topty)
              rs => pure rs

searchNames : {auto c : Ref Ctxt Defs} ->
              {auto m : Ref Meta (Metadata annot)} ->
              {auto u : Ref UST (UState annot)} ->
              annot -> SearchOpts -> Env Term vars ->
              Term vars -> Maybe ClosedTerm ->
              Maybe RecData -> List Name -> Core annot (List (Term vars))
searchNames loc opts env ty topty defining []
    = pure []
searchNames loc opts env ty topty defining (n :: ns)
    = do gam <- get Ctxt
         let visns = mapMaybe (visible (gamma gam) (currentNS gam)) (n :: ns)
         log 5 $ "Searching " ++ show (map fst visns) ++ " for " ++ show ty
         let nfty = nf gam env ty
         getSuccessful loc opts False env ty topty defining
            (map (searchName loc opts env nfty topty defining) visns)
  where
    visible : Gamma -> List String -> Name -> Maybe (Name, GlobalDef)
    visible gam nspace n
        = do def <- lookupGlobalExact n gam
             if visibleIn nspace n (visibility def)
                then Just (n, def)
                else Nothing

tryRecursive : {auto c : Ref Ctxt Defs} ->
               {auto m : Ref Meta (Metadata annot)} ->
               {auto u : Ref UST (UState annot)} ->
               annot -> SearchOpts -> 
               Env Term vars -> Term vars -> Maybe ClosedTerm ->
               Maybe RecData -> Core annot (List (Term vars))
tryRecursive loc opts env ty topty Nothing = pure []
tryRecursive loc opts env ty topty (Just rdata) 
    = do gam <- get Ctxt
         log 5 $ "Recursive: " ++ show (recname rdata) ++ " " ++ show (lhsapp rdata)
         case lookupGlobalExact (recname rdata) (gamma gam) of
              Nothing => pure []
              Just def =>
                do tms <- searchName loc opts env (nf gam env ty) topty Nothing
                                     (recname rdata, def)
                   gam <- get Ctxt
                   let tms = map (normaliseHoles gam env) tms
                   log 10 $ show tms
                   pure (filter (structDiff (lhsapp rdata)) tms)
  where
    mutual
      -- A fairly simple superficialy syntactic check to make sure that
      -- the recursive call is structurally different from the lhs
      -- (Essentially, meaning that there's a constructor application in
      -- one where there's a local in another, or that constructor applications
      -- differ somewhere)
      argDiff : Term vs -> Term vs' -> Bool
      argDiff (Local _ _) (Local _ _) = False
      argDiff (Ref _ fn) (Ref _ fn') = fn /= fn'
      argDiff (Bind _ _ _) (Bind _ _ _) = False
      argDiff (App f a) (App f' a') 
         = structDiff f f' || structDiff a a'
      argDiff (PrimVal c) (PrimVal c') = c /= c'
      argDiff Erased _ = False
      argDiff _ Erased = False
      argDiff TType TType = False
      argDiff _ _ = True
      
      appsDiff : Term vs -> Term vs' -> List (Term vs) -> List (Term vs') ->
                 Bool
      appsDiff (Ref (DataCon _ _) f) (Ref (DataCon _ _) f') args args'
         = if f == f' then or (map Delay (zipWith argDiff args args'))
                      else True
      appsDiff (Ref (TyCon _ _) f) (Ref (TyCon _ _) f') args args'
         = if f == f' then or (map Delay (zipWith argDiff args args'))
                      else True
      appsDiff (Ref _ f) (Ref _ f') args args'
         = if f == f' && length args == length args'
              then or (map Delay (zipWith argDiff args args'))
              else False -- can't be sure
      appsDiff (Ref (DataCon _ _) f) (Local _ _) _ _ = True
      appsDiff (Local _ _) (Ref (DataCon _ _) f) _ _ = True
      appsDiff f f' [] [] = argDiff f f'
      appsDiff _ _ _ _ = False -- can't be sure...

      -- Reject if the recursive call is the same in structure as the lhs
      structDiff : Term vs -> Term vs' -> Bool
      structDiff tm tm'
         = let (f, args) = getFnArgs tm
               (f', args') = getFnArgs tm' in
               appsDiff f f' args args'

-- A local is usable if it contains no holes in an argument position
usableLocal : {auto c : Ref Ctxt Defs} ->
              {auto m : Ref Meta (Metadata annot)} ->
              annot -> Env Term vars -> NF vars -> Core annot Bool
usableLocal loc env (NApp (NRef _ n) args)
    = do u <- nameIsHole loc n
         pure (not u)
usableLocal loc _ _ = pure True

searchLocalWith : {auto c : Ref Ctxt Defs} ->
                  {auto m : Ref Meta (Metadata annot)} ->
                  {auto u : Ref UST (UState annot)} ->
                  annot -> SearchOpts -> Env Term vars -> List (Term vars, Term vars) ->
                  Term vars -> Maybe ClosedTerm -> Maybe RecData -> 
                  Core annot (List (Term vars))
searchLocalWith loc opts env [] ty topty defining
    = pure []
searchLocalWith {vars} loc opts env ((p, pty) :: rest) ty topty defining
    = do gam <- get Ctxt
         getSuccessful loc opts False env ty topty defining
                       [findPos gam p id (nf gam env pty) ty,
                        searchLocalWith loc opts env rest ty
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
                then 
                  tryUnify -- try with no arguments first
                    (do [] <- unify InTerm loc env ty nty
                           | _ => throw (InternalError "Can't use directly")
                        pure (mkCandidates (f prf) []))
                    (do [] <- unify InTerm loc env ty appTy
                           | _ => pure []
                        args' <- traverse (searchIfHole loc opts defining topty env) 
                                          args
                        pure (mkCandidates (f prf) args'))
                else pure []

    findPos : Defs -> Term vars -> 
              (Term vars -> Term vars) ->
              NF vars -> Term vars -> Core annot (List (Term vars))
    findPos gam prf f x@(NTCon pn _ _ [xty, yty]) ty
        = getSuccessful loc opts False env ty topty defining
              [findDirect gam prf f x (nf gam env ty),
                 (do fname <- maybe (throw (InternalError "No fst"))
                                    pure
                                    (fstName gam)
                     sname <- maybe (throw (InternalError "No snd"))
                                    pure
                                    (sndName gam)
                     if isPairType pn gam
                        then getSuccessful loc opts False env ty topty defining
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
              {auto m : Ref Meta (Metadata annot)} ->
              {auto u : Ref UST (UState annot)} ->
              annot -> SearchOpts -> 
              Env Term vars -> Term vars -> Maybe ClosedTerm ->
              Maybe RecData -> Core annot (List (Term vars))
searchLocal loc opts env ty topty defining 
    = do defs <- get Ctxt
         searchLocalWith loc opts env (getAllEnv [] env) 
                         ty topty defining

searchType : {auto c : Ref Ctxt Defs} ->
             {auto m : Ref Meta (Metadata annot)} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> SearchOpts -> Env Term vars -> Maybe RecData ->
             Maybe ClosedTerm ->
             Nat -> Term vars -> Core annot (List (Term vars))
searchType loc opts env defining topty (S k) (Bind n (Pi c info ty) sc)
    = do let env' : Env Term (n :: _) = Pi c info ty :: env
         log 6 $ "Introduced lambda, search for " ++ show sc
         scVal <- searchType loc opts env' defining topty k sc
         pure (map (Bind n (Lam c info ty)) scVal)
searchType {vars} loc opts env defining topty Z (Bind n (Pi c info ty) sc)
    = -- try a local before creating a lambda...
      tryUnify 
           (searchLocal loc opts env (Bind n (Pi c info ty) sc) topty defining)
           (do log 6 $ "Introduced lambda, search for " ++ show sc
               defs <- get Ctxt
               let n' = UN (getArgName defs n vars (nf defs env ty))
               let env' : Env Term (n' :: _) = Pi c info ty :: env
               let sc' = renameTop n' sc
               scVal <- searchType loc opts env' defining topty Z sc'
               pure (map (Bind n' (Lam c info ty)) scVal))
searchType loc opts env defining topty _ ty
    = case getFnArgs ty of
           (Ref (TyCon t ar) n, args) =>
                do gam <- get Ctxt
                   if length args == ar
                     then do sd <- getSearchData loc True n
                             let (dets, opens, cons, chasers) =
                                    (detArgs sd, globalHints sd, directHints sd, indirectHints sd)
                             log 5 $ "Hints for " ++ show n ++ " : " ++ show cons
                             -- Solutions is either:
                             -- First try the locals,
                             -- Then try the hints in order
                             -- Then try a recursive call
                             getSuccessful loc opts True env ty topty defining
                                  ([searchLocal loc opts env ty topty defining,
                                    searchNames loc opts env ty topty defining
                                                (opens ++ cons ++ chasers)]
                                    ++ if recOK opts 
                                         then [tryRecursive loc opts env ty topty defining]
                                         else [])
                     else pure []
           _ => do log 5 $ "Searching locals only at " ++ show ty
                   getSuccessful loc opts True env ty topty defining 
                       ([searchLocal loc opts env ty topty defining]
                         ++ if recOK opts
                               then [tryRecursive loc opts env ty topty defining]
                               else [])

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
             {auto m : Ref Meta (Metadata annot)} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> SearchOpts -> Maybe RecData -> Name -> 
             Nat -> Maybe ClosedTerm ->
             Defs -> GlobalDef -> Core annot (List ClosedTerm)
searchHole loc opts defining n locs topty gam glob
    = do let searchty = normaliseScope gam [] (type glob)
         log 5 $ "Running search: " ++ show n ++ " in " ++ show (map recname defining) ++
                 " for " ++ show searchty
         dumpConstraints 5 True
         searchType loc opts [] defining topty locs searchty

-- Declared at the top
search loc opts defining topty n_in
    = do gam <- get Ctxt
         case lookupHoleName n_in (gamma gam) of
              Just (n, glob) =>
                   -- The definition should be 'BySearch' at this stage,
                   -- if it's arising from an auto implicit
                   case definition glob of
                        Hole locs False _ => searchHole loc opts defining n locs topty gam glob
                        BySearch _ _ => searchHole loc opts defining n 
                                                   (getArity gam [] (type glob)) 
                                                   topty gam glob
                        _ => do log 10 $ show n_in ++ " not a hole"
                                throw (InternalError $ "Not a hole: " ++ show n ++ " in " ++ show (map recname defining))
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

getLHSData : Defs -> Maybe ClosedTerm -> Maybe RecData
getLHSData defs Nothing = Nothing
getLHSData defs (Just tm) = getLHS (normaliseHoles defs [] tm)
  where
    getLHS : Term vars -> Maybe RecData
    getLHS (Bind _ (PVar _ _) sc) = getLHS sc
    getLHS (Bind _ (PLet _ _ _) sc) = getLHS sc
    getLHS sc 
        = case getFn sc of
               Ref _ n => Just (MkRecData n sc)
               _ => Nothing

dropLinearErrors : {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST (UState annot)} ->
                   annot -> List ClosedTerm ->
                   Core annot (List ClosedTerm)
dropLinearErrors loc [] = pure []
dropLinearErrors loc (t :: ts)
    = catch (do linearCheck loc Rig1 False [] t
                ts' <- dropLinearErrors loc ts
                pure (t :: ts'))
            (\err => dropLinearErrors loc ts)

export
exprSearch : {auto c : Ref Ctxt Defs} ->
             {auto m : Ref Meta (Metadata annot)} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Name -> List Name -> Core annot (List ClosedTerm)
exprSearch loc n hints
    = do lhs <- findHoleLHS n
         defs <- get Ctxt
         rs <- search loc (MkSearchOpts False True 5)
                (getLHSData defs lhs) Nothing n
         dropLinearErrors loc rs

