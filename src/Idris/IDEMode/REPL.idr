module Idris.IDEMode.REPL

import Compiler.Scheme.Chez
import Compiler.Scheme.Chicken
import Compiler.Scheme.Racket
import Compiler.Common

import Core.AutoSearch
import Core.CompileExpr
import Core.Context
import Core.InitPrimitives
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.TT
import Core.Unify

import Idris.Desugar
import Idris.Error
import Idris.ModTree
import Idris.Parser
import Idris.Resugar
import Idris.REPLCommon
import Idris.Syntax

import Idris.IDEMode.Parser
import Idris.IDEMode.Commands

import TTImp.CaseSplit
import TTImp.Elab
import TTImp.TTImp
import TTImp.ProcessTTImp
import TTImp.Reflect

import Control.Catchable
import System

data IDECommand
     = LoadFile String (Maybe Integer)
     | TypeOf String (Maybe (Integer, Integer))

getIDECommand : SExp -> Maybe IDECommand
getIDECommand (SExpList [SymbolAtom "load-file", StringAtom fname])
    = Just $ LoadFile fname Nothing
getIDECommand (SExpList [SymbolAtom "load-file", StringAtom fname, IntegerAtom l])
    = Just $ LoadFile fname (Just l)
getIDECommand (SExpList [SymbolAtom "type-of", StringAtom n])
    = Just $ TypeOf n Nothing
getIDECommand (SExpList [SymbolAtom "type-of", StringAtom n,
                         IntegerAtom l, IntegerAtom c])
    = Just $ TypeOf n (Just (l, c))
getIDECommand _ = Nothing

getMsg : SExp -> Maybe (IDECommand, Integer)
getMsg (SExpList [cmdexp, IntegerAtom num])
   = do cmd <- getIDECommand cmdexp
        pure (cmd, num)
getMsg _ = Nothing

getNChars : Nat -> IO (List Char)
getNChars Z = pure []
getNChars (S k)
    = do x <- getChar
         xs <- getNChars k
         pure (x :: xs)

hex : Char -> Maybe Int
hex '0' = Just 0
hex '1' = Just 1
hex '2' = Just 2
hex '3' = Just 3
hex '4' = Just 4
hex '5' = Just 5
hex '6' = Just 6
hex '7' = Just 7
hex '8' = Just 8
hex '9' = Just 9
hex 'a' = Just 10
hex 'b' = Just 11
hex 'c' = Just 12
hex 'd' = Just 13
hex 'e' = Just 14
hex 'f' = Just 15
hex _ = Nothing
    
toHex : Int -> List Char -> Maybe Int
toHex _ [] = Just 0
toHex m (d :: ds) 
    = pure $ !(hex (toLower d)) * m + !(toHex (m*16) ds)

-- Read 6 characters. If they're a hex number, read that many characters.
-- Otherwise, just read to newline
getInput : IO String
getInput 
    = do x <- getNChars 6
         case toHex 1 (reverse x) of
              Nothing =>
                do rest <- getLine
                   pure (pack x ++ rest)
              Just num =>
                do inp <- getNChars (cast num)
                   pure (pack inp)

process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState FC)} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref Meta (Metadata FC)} ->
          {auto o : Ref ROpts REPLOpts} ->
          IDECommand -> Core FC ()
process (LoadFile fname toline) 
    = printError "Not implemented"
process (TypeOf n pos) 
    = printError "Not implemented"

repl : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST (UState FC)} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto m : Ref Meta (Metadata FC)} ->
       {auto o : Ref ROpts REPLOpts} ->
       Core FC ()
repl
    = do inp <- coreLift getInput
         end <- coreLift $ fEOF stdin
         if end
            then pure ()
            else case parseSExp inp of
                      Left err =>
                         do printError ("Parse error: " ++ show err)
                            repl
                      Right sexp =>
                         case getMsg sexp of
                              Just (cmd, i) => 
                                 do setOutput (IDEMode i)
                                    process cmd
                                    repl
                              Nothing => 
                                 do printError "Unrecognised command"
                                    repl

export
replIDE : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState FC)} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref Meta (Metadata FC)} ->
          {auto o : Ref ROpts REPLOpts} ->
          Core FC ()
replIDE = 
    do send (version 2 0)
       repl

