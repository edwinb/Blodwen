module Idris.IDEMode.CaseSplit

import Core.Context
import Core.Metadata
import Core.TT

import TTImp.CaseSplit
import TTImp.TTImp
import TTImp.Utils

import Parser.Unlit

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

doUpdates : Defs -> List (String, String) -> List SourcePart -> 
            State (List String) (List SourcePart)
doUpdates defs ups [] = pure []
doUpdates defs ups (LBrace :: xs)
    = case dropSpace xs of
           Name n :: RBrace :: rest =>
                pure (LBrace :: Name n :: 
                      Whitespace " " :: Equal :: Whitespace " " ::
                      !(doUpdates defs ups (Name n :: RBrace :: rest)))
           Name n :: Equal :: rest =>
                pure (LBrace :: Name n ::
                      Whitespace " " :: Equal :: Whitespace " " ::
                      !(doUpdates defs ups rest))
           _ => pure (LBrace :: !(doUpdates defs ups xs))
  where
    dropSpace : List SourcePart -> List SourcePart
    dropSpace [] = []
    dropSpace (RBrace :: xs) = RBrace :: xs
    dropSpace (Whitespace _ :: xs) = dropSpace xs
    dropSpace (x :: xs) = x :: dropSpace xs
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

getEnvArgNames : Defs -> Nat -> NF [] -> List String
getEnvArgNames defs Z sc = getArgNames defs [] [] sc
getEnvArgNames defs (S k) (NBind n _ sc)
    = getEnvArgNames defs k (sc (MkClosure defaultOpts [] [] Erased))
getEnvArgNames defs n ty = []

mutual
  fnGenName : Bool -> GenName -> String
  fnGenName lhs (Nested _ n) = fnName lhs n
  fnGenName lhs (CaseBlock n _) = fnName lhs n
  fnGenName lhs (WithBlock n _) = fnName lhs n

  fnName : Bool -> Name -> String
  fnName lhs (UN n) 
      = if any (not . identChar) (unpack n)
           then if lhs then "(" ++ n ++ ")"
                       else "op"
           else n
  fnName lhs (NS _ n) = fnName lhs n
  fnName lhs (DN s _) = s
  fnName lhs (GN g) = fnGenName lhs g
  fnName lhs n = show n

export
getClause : {auto c : Ref Ctxt Defs} ->
            {auto m : Ref Meta (Metadata FC)} ->
            {auto o : Ref ROpts REPLOpts} ->
            Int -> Name -> Core FC (Maybe String)
getClause l n
    = do defs <- get Ctxt
         Just (loc, n, envlen, ty) <- findTyDeclAt (\p, n => onLine (l-1) p)
             | Nothing => pure Nothing
         let argns = getEnvArgNames defs envlen (nf defs [] ty)
         Just srcLine <- getSourceLine l
           | Nothing => pure Nothing
         let (lit, src) = isLit srcLine
         pure (Just (indent lit loc ++ fnName True n ++ concat (map (" " ++) argns) ++
                  " = ?" ++ fnName False n ++ "_rhs"))
  where
    indent : Bool -> FC -> String
    indent True fc = ">" ++ pack (replicate (cast (max 0 (snd (startPos fc) - 1))) ' ')
    indent False fc = pack (replicate (cast (snd (startPos fc))) ' ')
