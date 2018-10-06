module TTImp.CaseSplit

import Core.Context
import Core.Metadata
import Core.Normalise
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
     CantSplitThis : Name -> SplitError -- Request to split was not on a splittable variable
     CantFindLHS : SplitError -- Can't find any clause to split

export
Show SplitError where
  show NoValidSplit = "No valid case splits"
  show (CantSplitThis n) = "Can't split on " ++ show n
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
    = if n == x
         then case nf defs env ty of
                   NTCon tyn _ _ _ => Just tyn
                   _ => Nothing
         else findTyName defs (PVar c ty :: env) n sc
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
           Nothing => pure (SplitFail (CantSplitThis n))
           Just fn =>
              do defs <- get Ctxt
                 case findTyName defs [] n lhs of
                      Nothing => pure (SplitFail (CantSplitThis n))
                      Just tyn =>
                          case lookupDefExact tyn (gamma defs) of
                               Just (TCon _ _ _ _ cons) => pure (OK (fn, tyn, cons))
                               _ => pure (SplitFail (CantSplitThis n))

findAllVars : Term vars -> List Name
findAllVars (Bind x (PVar c ty) sc)
    = x :: findAllVars sc
findAllVars _ = []

unique : String -> Int -> List Name -> String
unique str suff usedns
    = let var = mkVarN str suff in
          if UN var `elem` usedns
             then unique str (suff + 1) usedns
             else var
  where
    mkVarN : String -> Int -> String
    mkVarN x 0 = x
    mkVarN x i = x ++ show i

getArgNames : List Name -> Env Term vars -> NF vars -> List String
getArgNames allvars env (NBind x (Pi _ p ty) sc) 
    = let argns = getArgNames allvars env 
                              (sc (MkClosure defaultOpts [] env Erased)) in
          case p of
               Explicit => getName x (allvars ++ map UN argns) :: argns
               _ => argns
  where
    getName : Name -> List Name -> String
    getName (UN n) used = unique n 0 used
    getName _ used = unique "x" 0 used
getArgNames allvars env val = []

expandCon : {auto c : Ref Ctxt Defs} ->
            annot -> List Name -> Name -> Core annot (RawImp annot)
expandCon loc usedvars con
    = do defs <- get Ctxt
         case lookupTyExact con (gamma defs) of
              Nothing => throw (UndefinedName loc con)
              Just ty => pure (apply (IVar loc con) 
                                  (map (IBindVar loc)
                                       (getArgNames usedvars [] (nf defs [] ty))))

-- Return a new LHS to check, replacing 'var' with an application of 'con'
-- Also replace any variables with '_' to allow elaboration to
-- expand them
newLHS : {auto c : Ref Ctxt Defs} ->
         annot -> 
         List Name -> -- all the variable names
         (var : Name) -> (con : Name) -> 
         RawImp annot -> Core annot (RawImp annot)
newLHS fc allvars var con (IVar loc n)
    = if n `elem` allvars
         then if n == var
                 then expandCon loc allvars con
                 else pure $ Implicit loc
         else pure $ IVar loc n
newLHS fc allvars var con (IApp loc f a)
    = pure $ IApp loc !(newLHS loc allvars var con f) 
                      !(newLHS loc allvars var con a)
newLHS fc allvars var con (IImplicitApp loc f n a)
    = pure $ IImplicitApp loc !(newLHS loc allvars var con f) n 
                              !(newLHS loc allvars var con a)
newLHS fc allvars var con (IAs loc n p)
    = newLHS loc allvars var con p
newLHS fc allvars var con _ = pure $ Implicit fc

record Updates annot where
  constructor MkUpdates
  namemap : List (Name, Name)
  updates : List (Name, RawImp annot)

findUpdates : RawImp annot -> RawImp annot -> State (Updates annot) ()
findUpdates (IVar _ n) (IVar loc n')
    = do u <- get
         case lookup n' (namemap u) of
              Nothing => put (record { namemap $= ((n', n) ::) } u)
              Just nm => put (record { updates $= ((n, IVar loc nm) ::) } u)
findUpdates (IVar loc n) tm
    = do u <- get
         let nupdates = map (\x => (fst x, IVar loc (snd x))) (namemap u)
         put (record { updates $= ((n, substNames [] nupdates tm) ::) } u)
findUpdates (IApp _ f a) (IApp _ f' a')
    = do findUpdates f f'
         findUpdates a a'
findUpdates (IImplicitApp _ f _ a) (IImplicitApp _ f' _ a')
    = do findUpdates f f'
         findUpdates a a'
findUpdates (IImplicitApp _ f _ a) f' = findUpdates f f'
findUpdates f (IImplicitApp _ f' _ a) = findUpdates f f'
findUpdates _ _ = pure ()

getUpdates : RawImp annot -> RawImp annot -> List (Name, RawImp annot)
getUpdates orig new
    = updates $ execState (findUpdates orig new) (MkUpdates [] [])

mkCase : {auto c : Ref Ctxt Defs} ->
         (Reflect annot, Reify annot) =>
         Name -> RawImp annot -> RawImp annot -> Core annot (ClauseUpdate annot)
mkCase {c} fn orig lhs_raw
    = do u <- newRef UST initUState
         i <- newRef ImpST initImpState
         m <- newRef Meta initMetadata
         defs <- get Ctxt
         handleClause
           (do (lhs_in, _, _) <- inferTerm {c} {u} {i} {m}
                                           (\c, u, i, m => processDecl {c} {u} {i} {m})
                                           False fn [] (MkNested [])
                                           PATTERN InLHS lhs_raw
               let lhs = normaliseHoles defs [] lhs_in
               put Ctxt defs -- reset the context, we don't want any updates

               lhs' <- unelab (getAnnot lhs_raw) [] lhs
               pure (Valid lhs' (getUpdates orig lhs')))
           (\err => case err of
                         WhenUnifying _ env l r err
                            => do gam <- get Ctxt
                                  if impossibleOK gam (nf gam env l) (nf gam env r)
                                     then pure (Impossible lhs_raw)
                                     else pure Invalid
                         _ => pure Invalid)

substLets : Term vars -> Term vars
substLets (Bind n (Let c val ty) sc) = substLets (subst val sc)
substLets (Bind n b sc) = Bind n b (substLets sc)
substLets tm = tm

combine : List (ClauseUpdate annot) -> List (ClauseUpdate annot) ->
          SplitResult (List (ClauseUpdate annot))
combine [] [] = SplitFail NoValidSplit
combine [] acc = OK (reverse acc)
combine (Invalid :: xs) acc = combine xs acc
combine (x :: xs) acc = combine xs (x :: acc)

export
getSplits : {auto m : Ref Meta (Metadata annot)} ->
            {auto c : Ref Ctxt Defs} ->
            (Reflect annot, Reify annot) =>
            (annot -> Bool) -> Name -> 
            Core annot (SplitResult (List (ClauseUpdate annot)))
getSplits p n
    = do Just (loc, lhs_in) <- findLHSAt p
              | Nothing => pure (SplitFail CantFindLHS)
         let lhs = substLets lhs_in
         let usedns = findAllVars lhs

         defs <- get Ctxt
         OK (fn, tyn, cons) <- findCons n lhs
            | SplitFail err => pure (SplitFail err)
        
         rawlhs <- unelab loc [] lhs
         trycases <- traverse (\c => newLHS loc usedns n c rawlhs) cons

         cases <- traverse (mkCase fn rawlhs) trycases

         pure (combine cases [])
