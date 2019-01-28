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
import Idris.REPL
import Idris.Syntax

import Idris.IDEMode.Parser
import Idris.IDEMode.Commands

import TTImp.CaseSplit
import TTImp.Elab
import TTImp.TTImp
import TTImp.ProcessTTImp
import TTImp.Reflect

import Control.Catchable
-- import System

import CompilerRuntime

getNChars : Nat -> BIO (List Char)
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
getInput : BIO String
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
process (Interpret cmd)
    = do interpret cmd
         printResult "Done"
process (LoadFile fname toline) 
    = do opts <- get ROpts
         put ROpts (record { mainfile = Just fname } opts)
         resetContext
         errs <- buildDeps fname
         updateErrorLine errs
         Right res <- coreLift (readFile fname)
            | Left err => setSource ""
         setSource res
         case errs of
              [] => printResult $ "Loaded " ++ fname
              _ => printError $ "Failed to load " ++ fname
process (TypeOf n Nothing) 
    = do Idris.REPL.process (Check (PRef replFC (UN n)))
         pure ()
process (TypeOf n (Just (l, c)))
    = do Idris.REPL.process (Editing (TypeAt (fromInteger l) (fromInteger c) (UN n)))
         pure ()
process (CaseSplit l c n)
    = do Idris.REPL.process (Editing (CaseSplit (fromInteger l) (fromInteger c) (UN n)))
         pure ()
process (AddClause l n)
    = do Idris.REPL.process (Editing (AddClause (fromInteger l) (UN n)))
         pure ()
process (ExprSearch l n hs all)
    = do Idris.REPL.process (Editing (ExprSearch (fromInteger l) (UN n) 
                                                 (map UN hs) all))
         pure ()
process (GenerateDef l n)
    = do Idris.REPL.process (Editing (GenerateDef (fromInteger l) (UN n)))
         pure ()
process (MakeLemma l n)
    = do Idris.REPL.process (Editing (MakeLemma (fromInteger l) (UN n)))
         pure ()
process (MakeCase l n)
    = do Idris.REPL.process (Editing (MakeCase (fromInteger l) (UN n)))
         pure ()
process (MakeWith l n)
    = do Idris.REPL.process (Editing (MakeWith (fromInteger l) (UN n)))
         pure ()

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState FC)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref Meta (Metadata FC)} ->
               {auto o : Ref ROpts REPLOpts} ->
               IDECommand -> Core FC ()
processCatch cmd
    = do c' <- get Ctxt
         u' <- get UST
         s' <- get Syn
         o' <- get ROpts
         catch (process cmd)
               (\err => do put Ctxt c'
                           put UST u'
                           put Syn s'
                           put ROpts o'
                           emitError err
                           printError "Command failed")

loop : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST (UState FC)} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto m : Ref Meta (Metadata FC)} ->
       {auto o : Ref ROpts REPLOpts} ->
       Core FC ()
loop
    = do inp <- coreLift getInput
         end <- coreLift $ fEOF stdin
         if end
            then pure ()
            else case parseSExp inp of
                      Left err =>
                         do printError ("Parse error: " ++ show err)
                            loop
                      Right sexp =>
                         case getMsg sexp of
                              Just (cmd, i) => 
                                 do setOutput (IDEMode i)
                                    processCatch cmd
                                    loop
                              Nothing => 
                                 do printError "Unrecognised command"
                                    loop

export
replIDE : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState FC)} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref Meta (Metadata FC)} ->
          {auto o : Ref ROpts REPLOpts} ->
          Core FC ()
replIDE = 
    do send (version 2 0)
       loop

