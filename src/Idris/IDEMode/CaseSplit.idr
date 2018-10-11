module Idris.IDEMode.CaseSplit

import Core.Context
import Core.TT

import TTImp.CaseSplit
import TTImp.TTImp

import Idris.IDEMode.TokenLine
import Idris.REPLOpts
import Idris.Resugar
import Idris.Syntax

import Control.Monad.State

%default covering

getLine : Nat -> List String -> Maybe String
getLine Z (l :: ls) = Just l
getLine (S k) (l :: ls) = getLine k ls
getLine _ [] = Nothing

toStrUpdate : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              (Name, RawImp FC) -> Core FC (List (String, String))
toStrUpdate (UN n, term)
    = do clause <- pterm term
         pure [(n, show (bracket clause))]
  where
    bracket : PTerm -> PTerm
    bracket tm@(PRef _ _) = tm
    bracket tm@(PList _ _) = tm
    bracket tm@(PPair _ _ _) = tm
    bracket tm@(PUnit _) = tm
    bracket tm@(PComprehension _ _ _) = tm
    bracket tm@(PPrimVal _ _) = tm
    bracket tm = PBracketed emptyFC tm
toStrUpdate _ = pure [] -- can't replace non user names

dump : SourcePart -> String
dump (Whitespace str) = str
dump (Name n) = n
dump (HoleName n) = "?" ++ n
dump LBrace = "{"
dump RBrace = "}"
dump Equal = "="
dump (Other str) = str

nameNum : String -> (String, Int)
nameNum str
    = case span isDigit (reverse str) of
           ("", _) => (str, 0)
           (nums, pre)
              => case unpack pre of
                      ('_' :: rest) => (reverse (pack rest), cast (reverse nums))
                      _ => (str, 0)

uniqueName : Defs -> List String -> String -> String
uniqueName defs used n
    = if usedName 
         then uniqueName defs used (next n)
         else n
  where
    usedName : Bool
    usedName 
        = case lookupTyName (UN n) (gamma defs) of
               [] => n `elem` used
               _ => True

    next : String -> String
    next str 
        = let (n, i) = nameNum str in
              n ++ "_" ++ show (i + 1)

doUpdates : Defs -> List (String, String) -> List SourcePart -> 
            State (List String) (List SourcePart)
doUpdates defs ups [] = pure []
doUpdates defs ups (Name n :: xs)
    = case lookup n ups of
           Nothing => pure (Name n :: !(doUpdates defs ups xs))
           Just up => pure (Other up :: !(doUpdates defs ups xs))
doUpdates defs ups (HoleName n :: xs)
    = do used <- get
         let n' = uniqueName defs used n
         put (n' :: used)
         pure $ HoleName n' :: !(doUpdates defs ups xs)
doUpdates defs ups (x :: xs) 
    = pure $ x :: !(doUpdates defs ups xs)

-- State here is a list of new hole names we generated (so as not to reuse any).
-- Update the token list with the string replacements for each match, and return 
-- the newly generated strings.
updateAll : Defs -> List SourcePart -> List (List (String, String)) -> 
            State (List String) (List String)
updateAll defs l [] = pure []
updateAll defs l (rs :: rss)
    = do l' <- doUpdates defs rs l
         rss' <- updateAll defs l rss
         pure (concat (map dump l') :: rss')

-- Turn the replacements we got from 'getSplits' into a list of actual string
-- replacements
getReplaces : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto o : Ref ROpts REPLOpts} ->
              List (Name, RawImp FC) -> Core FC (List (String, String))
getReplaces updates
    = do strups <- traverse toStrUpdate updates
         pure (concat strups)
         
showImpossible : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 RawImp FC -> Core FC String
showImpossible lhs
    = do clause <- pterm lhs
         pure (show clause ++ " impossible")

-- Given a list of updates and a line and column, find the relevant line in
-- the source file and return the lines to replace it with
export
updateCase : {auto c : Ref Ctxt Defs} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto o : Ref ROpts REPLOpts} ->
             List (ClauseUpdate FC) -> Int -> Int ->
             Core FC (List String)
updateCase splits line col
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => throw (InternalError "No file loaded")
              Just f =>
                do Right file <- coreLift $ readFile f
                       | Left err => throw (FileErr f err)
                   let thisline = getLine (cast line) (lines file)
                   case thisline of
                        Nothing => throw (InternalError "File too short!")
                        Just l => 
                            do let valid = mapMaybe getValid splits
                               let bad = mapMaybe getBad splits
                               if isNil valid
                                  then traverse showImpossible bad
                                  else do rs <- traverse getReplaces valid
                                          let stok = tokens l
                                          defs <- get Ctxt
                                          pure (evalState (updateAll defs stok rs) [])
  where
    getValid : ClauseUpdate FC -> Maybe (List (Name, RawImp FC))
    getValid (Valid _ ups) = Just ups
    getValid _ = Nothing

    getBad : ClauseUpdate FC -> Maybe (RawImp FC)
    getBad (Impossible lhs) = Just lhs
    getBad _ = Nothing
