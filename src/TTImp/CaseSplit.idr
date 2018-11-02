module TTImp.CaseSplit

import Core.Context
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.Reflect
import Core.TT
import Core.UnifyState

import TTImp.Elab
import TTImp.Elab.State
import TTImp.Elab.Unelab
import TTImp.ProcessDef
import TTImp.ProcessTTImp
import TTImp.TTImp
import TTImp.Utils

import Control.Monad.State

%default covering

-- The result of a request to case split is a list of string updates, i.e. edits
-- on the clause in the source file, which an interactive editor can deal with
-- however it sees fit. 'Valid' means that the result will type check,
-- 'Impossible' means that the result will be a valid 'impossible' case
public export
data ClauseUpdate : Type -> Type where
     Valid : RawImp annot -> List (Name, RawImp annot) -> ClauseUpdate annot
     Impossible : RawImp annot -> ClauseUpdate annot
     Invalid : ClauseUpdate annot

export
Show (ClauseUpdate annot) where
  show (Valid lhs updates) = "Valid: " ++ show lhs ++ "\n" ++ "Updates: " ++ show updates
  show (Impossible lhs) = "Impossible: " ++ show lhs
  show Invalid = "Invalid"

public export 
data SplitError : Type where
     NoValidSplit : SplitError -- None of the splits either type check, or fail
                               -- in a way which is valid as an 'impossible' case
     CantSplitThis : Name -> String -> SplitError -- Request to split was not on a splittable variable
     CantFindLHS : SplitError -- Can't find any clause to split

export
Show SplitError where
  show NoValidSplit = "No valid case splits"
  show (CantSplitThis n r) = "Can't split on " ++ show n ++ " (" ++ r ++ ")"
  show CantFindLHS = "No clause to split here"

public export
data SplitResult : Type -> Type where
     SplitFail : SplitError -> SplitResult a
     OK : a -> SplitResult a

export
Show a => Show (SplitResult a) where
  show (SplitFail err) = "Split error: " ++ show err
  show (OK res) = "OK: " ++ show res

findTyName : Defs -> Env Term vars -> Name -> Term vars -> Maybe Name
findTyName defs env n (Bind x (PVar c ty) sc)
      -- Take the first one, which is the most recently bound
    = if n == x
         then case nf defs env ty of
                   NTCon tyn _ _ _ => Just tyn
                   _ => Nothing
         else findTyName defs (PVar c ty :: env) n sc
findTyName defs env n (Bind x b sc) = findTyName defs (b :: env) n sc
findTyName _ _ _ _ = Nothing

getDefining : Term vars -> Maybe Name
getDefining (Bind _ _ sc) = getDefining sc
getDefining tm
    = case getFn tm of
           Ref _ fn => Just fn
           _ => Nothing

findCons : {auto c : Ref Ctxt Defs} ->
           Name -> Term [] -> Core annot (SplitResult (Name, Name, List Name))
findCons n lhs
    = case getDefining lhs of
           Nothing => pure (SplitFail 
                            (CantSplitThis n "Can't find function name on LHS"))
           Just fn =>
              do defs <- get Ctxt
                 case findTyName defs [] n lhs of
                      Nothing => pure (SplitFail (CantSplitThis n 
                                         ("Can't find name " ++ show n ++ " in LHS")))
                      Just tyn =>
                          case lookupDefExact tyn (gamma defs) of
                               Just (TCon _ _ _ _ cons) => pure (OK (fn, tyn, cons))
                               res => pure (SplitFail 
                                            (CantSplitThis n 
                                               ("Not a type constructor " ++ 
                                                  show res)))

findAllVars : Term vars -> List Name
findAllVars (Bind x (PVar c ty) sc)
    = x :: findAllVars sc
findAllVars _ = []

unique : List String -> List String -> Int -> List Name -> String
unique [] supply suff usedns = unique supply supply (suff + 1) usedns
unique (str :: next) supply suff usedns
    = let var = mkVarN str suff in
          if UN var `elem` usedns
             then unique next supply suff usedns
             else var
  where
    mkVarN : String -> Int -> String
    mkVarN x 0 = x
    mkVarN x i = x ++ show i

defaultNames : List String
defaultNames = ["x", "y", "z", "w", "v", "s", "t", "u"]

export
getArgName : Defs -> Name -> List Name -> NF vars -> String
getArgName defs x allvars ty 
    = let defnames = findNames ty in
          getName x defnames allvars
  where
    findNames : NF vars -> List String
    findNames (NBind x (Pi _ _ _) _) = ["f", "g"]
    findNames (NTCon n _ _ _)
        = case lookup n (namedirectives (options defs)) of
               Nothing => defaultNames
               Just ns => ns
    findNames ty = defaultNames

    getName : Name -> List String -> List Name -> String
    getName (UN n) defs used = unique (n :: defs) (n :: defs) 0 used
    getName _ defs used = unique defs defs 0 used

export
getArgNames : Defs -> List Name -> Env Term vars -> NF vars -> List String
getArgNames defs allvars env (NBind x (Pi _ p ty) sc) 
    = let ns = case p of
                   Explicit => [getArgName defs x allvars ty]
                   _ => [] in
          ns ++ getArgNames defs (map UN ns ++ allvars) env 
                            (sc (MkClosure defaultOpts [] env Erased))
getArgNames defs allvars env val = []

expandCon : {auto c : Ref Ctxt Defs} ->
            annot -> List Name -> Name -> Core annot (RawImp annot)
expandCon loc usedvars con
    = do defs <- get Ctxt
         case lookupTyExact con (gamma defs) of
              Nothing => throw (UndefinedName loc con)
              Just ty => pure (apply (IVar loc con) 
                                  (map (IBindVar loc)
                                       (getArgNames defs usedvars [] 
                                                    (nf defs [] ty))))

updateArg : {auto c : Ref Ctxt Defs} ->
            annot -> 
            List Name -> -- all the variable names
            (var : Name) -> (con : Name) -> 
            RawImp annot -> Core annot (RawImp annot)
updateArg fc allvars var con (IVar loc n)
    = if n `elem` allvars
         then if n == var
                 then expandCon loc (filter (/= n) allvars) con
                 else pure $ Implicit loc
         else pure $ IVar loc n
updateArg fc allvars var con (IApp loc f a)
    = pure $ IApp loc !(updateArg loc allvars var con f) 
                      !(updateArg loc allvars var con a)
updateArg fc allvars var con (IImplicitApp loc f n a)
    = pure $ IImplicitApp loc !(updateArg loc allvars var con f) n 
                              !(updateArg loc allvars var con a)
updateArg fc allvars var con (IAs loc n p)
    = updateArg loc allvars var con p
updateArg fc allvars var con _ = pure $ Implicit fc

data ArgType annot
    = Explicit annot (RawImp annot)
    | Implicit annot (Maybe Name) (RawImp annot)

update : {auto c : Ref Ctxt Defs} ->
         annot -> 
         List Name -> -- all the variable names
         (var : Name) -> (con : Name) -> 
         ArgType annot -> Core annot (ArgType annot)
update locs allvars var con (Explicit loc arg)
    = pure $ Explicit loc !(updateArg locs allvars var con arg)
update locs allvars var con (Implicit loc n arg)
    = pure $ Implicit loc n !(updateArg locs allvars var con arg)

getFnArgs : RawImp annot -> List (ArgType annot) ->
            (RawImp annot, List (ArgType annot))
getFnArgs (IApp loc tm a) args
    = getFnArgs tm (Explicit loc a :: args)
getFnArgs (IImplicitApp loc tm n a) args
    = getFnArgs tm (Implicit loc n a :: args)
getFnArgs tm args = (tm, args)

apply : RawImp annot -> List (ArgType annot) -> RawImp annot
apply f (Explicit loc a :: args) = apply (IApp loc f a) args
apply f (Implicit loc n a :: args) = apply (IImplicitApp loc f n a) args
apply f [] = f

-- Return a new LHS to check, replacing 'var' with an application of 'con'
-- Also replace any variables with '_' to allow elaboration to
-- expand them
newLHS : {auto c : Ref Ctxt Defs} ->
         annot -> 
         Nat -> -- previous environment length; leave these alone
         List Name -> -- all the variable names
         (var : Name) -> (con : Name) -> 
         RawImp annot -> Core annot (RawImp annot)
newLHS loc envlen allvars var con tm
    = do let (f, args) = getFnArgs tm []
         let keep = map (const (Explicit loc (Implicit loc))) (take envlen args)
         let ups = drop envlen args
         ups' <- traverse (update loc allvars var con) ups
         pure $ apply f (keep ++ ups')

record Updates annot where
  constructor MkUpdates
  namemap : List (Name, Name)
  updates : List (Name, RawImp annot)

recordUpdate : annot -> Name -> RawImp annot -> State (Updates annot) ()
recordUpdate loc n tm
    = do u <- get
         let nupdates = map (\x => (fst x, IVar loc (snd x))) (namemap u)
         put (record { updates $= ((n, substNames [] nupdates tm) ::) } u)

findUpdates : Defs -> RawImp annot -> RawImp annot -> State (Updates annot) ()
findUpdates defs (IVar loc n) (IVar _ n')
    = case lookupTyExact n' (gamma defs) of
           Just _ => recordUpdate loc n (IVar loc n')
           Nothing =>
              do u <- get
                 case lookup n' (namemap u) of
                      Nothing => put (record { namemap $= ((n', n) ::) } u)
                      Just nm => put (record { updates $= ((n, IVar loc nm) ::) } u)
findUpdates defs (IVar loc n) tm = recordUpdate loc n tm
findUpdates defs (IApp _ f a) (IApp _ f' a')
    = do findUpdates defs f f'
         findUpdates defs a a'
findUpdates defs (IImplicitApp _ f _ a) (IImplicitApp _ f' _ a')
    = do findUpdates defs f f'
         findUpdates defs a a'
findUpdates defs (IImplicitApp _ f _ a) f' = findUpdates defs f f'
findUpdates defs f (IImplicitApp _ f' _ a) = findUpdates defs f f'
findUpdates _ _ _ = pure ()

getUpdates : Defs -> RawImp annot -> RawImp annot -> List (Name, RawImp annot)
getUpdates defs orig new
    = updates $ execState (findUpdates defs orig new) (MkUpdates [] [])

mkCase : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST (UState annot)} ->
         (Reflect annot, Reify annot) =>
         Name -> RawImp annot -> RawImp annot -> Core annot (ClauseUpdate annot)
mkCase {c} {u} fn orig lhs_raw
    = do i <- newRef ImpST initImpState
         m <- newRef Meta initMetadata
         defs <- get Ctxt
         ust <- get UST
         handleClause
           (do (lhs, _, _) <- inferTerm {c} {u} {i} {m}
                                        (\c, u, i, m => processDecl {c} {u} {i} {m})
                                        False fn [] (MkNested [])
                                        PATTERN (InLHS Rig1) lhs_raw
               put Ctxt defs -- reset the context, we don't want any updates
               put UST ust

               lhs' <- unelabNoSugar (getAnnot lhs_raw) [] lhs
               pure (Valid lhs' (getUpdates defs orig lhs')))
           (\err => case err of
                         WhenUnifying _ env l r err
                            => do gam <- get Ctxt
                                  if impossibleOK gam (nf gam env l) (nf gam env r)
                                     then pure (Impossible lhs_raw)
                                     else pure Invalid
                         _ => pure Invalid)

substLets : Term vars -> Term vars
substLets (Bind n (Let c val ty) sc) = substLets (subst val sc)
substLets (Bind n (PLet c val ty) sc) = substLets (subst val sc)
substLets (Bind n b sc) = Bind n b (substLets sc)
substLets tm = tm

combine : List (ClauseUpdate annot) -> List (ClauseUpdate annot) ->
          SplitResult (List (ClauseUpdate annot))
combine [] [] = SplitFail NoValidSplit
combine [] acc = OK (reverse acc)
combine (Invalid :: xs) acc = combine xs acc
combine (x :: xs) acc = combine xs (x :: acc)

export
getSplitsLHS : {auto m : Ref Meta (Metadata annot)} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState annot)} ->
               (Reflect annot, Reify annot) =>
               annot -> Nat -> ClosedTerm -> Name -> 
               Core annot (SplitResult (List (ClauseUpdate annot)))
getSplitsLHS loc envlen lhs_in n
    = do let lhs = substLets lhs_in
         let usedns = findAllVars lhs

         defs <- get Ctxt
         OK (fn, tyn, cons) <- findCons n lhs
            | SplitFail err => pure (SplitFail err)
        
         rawlhs <- unelabNoSugar loc [] lhs
         trycases <- traverse (\c => newLHS loc envlen usedns n c rawlhs) cons

         cases <- traverse (mkCase fn rawlhs) trycases

         pure (combine cases [])

export
getSplits : {auto m : Ref Meta (Metadata annot)} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST (UState annot)} ->
            (Reflect annot, Reify annot) =>
            (annot -> ClosedTerm -> Bool) -> Name -> 
            Core annot (SplitResult (List (ClauseUpdate annot)))
getSplits p n
    = do Just (loc, envlen, lhs_in) <- findLHSAt p
              | Nothing => pure (SplitFail CantFindLHS)
         getSplitsLHS loc envlen lhs_in n
