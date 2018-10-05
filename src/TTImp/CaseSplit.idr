module TTImp.CaseSplit

import Core.Context
import Core.Metadata
import Core.Normalise
import Core.TT

import TTImp.Elab
import TTImp.Elab.Unelab
import TTImp.ProcessDef
import TTImp.TTImp

-- The result of a request to case split is a list of string updates, i.e. edits
-- on the clause in the source file, which an interactive editor can deal with
-- however it sees fit. 'Valid' means that the result will type check,
-- 'Impossible' means that the result will be a valid 'impossible' case
public export
data ClauseUpdate : Type where
     Valid : List (String, String) -> ClauseUpdate
     Impossible : List (String, String) -> ClauseUpdate

public export 
data SplitError : Type where
     NoValidSplit : SplitError -- None of the splits either type check, or fail
                               -- in a way which is valid as an 'impossible' case
     CantSplitThis : SplitError -- Request to split was not on a splittable variable

public export
data SplitResult : Type -> Type where
     SplitFail : SplitError -> SplitResult a
     OK : a -> SplitResult a

findTyName : Defs -> Env Term vars -> Name -> Term vars -> Maybe Name
findTyName defs env n (Bind x (PVar c ty) sc)
    = if n == x
         then case nf defs env ty of
                   NTCon tyn _ _ _ => Just tyn
                   _ => Nothing
         else findTyName defs (PVar c ty :: env) n sc
findTyName _ _ _ _ = Nothing

findCons : {auto c : Ref Ctxt Defs} ->
           Name -> Term [] -> Core annot (SplitResult (Name, List Name))
findCons n lhs
    = do defs <- get Ctxt
         case findTyName defs [] n lhs of
              Nothing => pure (SplitFail CantSplitThis)
              Just tyn =>
                  do coreLift $ putStrLn $ "Found " ++ show tyn
                     case lookupDefExact tyn (gamma defs) of
                       Just (TCon _ _ _ _ cons) => pure (OK (tyn, cons))
                       _ => pure (SplitFail CantSplitThis)


export
getSplits : {auto m : Ref Meta (Metadata annot)} ->
            {auto c : Ref Ctxt Defs} ->
            (annot -> Bool) -> Name -> Core annot (SplitResult (List ClauseUpdate))
getSplits p n
    = do Just (loc, lhs) <- findLHSAt p
              | Nothing => pure (SplitFail CantSplitThis)
         defs <- get Ctxt
         OK (tyn, cons) <- findCons n lhs
            | SplitFail err => do coreLift $ putStrLn "oops"
                                  pure (SplitFail err)
        
         rawlhs <- unelab loc [] lhs
         coreLift $ printLn rawlhs
         coreLift $ printLn tyn
         coreLift $ printLn cons
         pure (SplitFail NoValidSplit)
