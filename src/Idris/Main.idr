module Main

import Core.Binary
import Core.Context
import Core.Core
import Core.Directory
import Core.InitPrimitives
import Core.Options
import Core.Unify

import Idris.CommandLine
import Idris.Desugar
import Idris.ModTree
import Idris.Syntax
import Idris.Parser
import Idris.ProcessIdr
import Idris.REPL

import Data.Vect
import System

import BlodwenPaths

%default covering

findInput : List CLOpt -> Maybe String
findInput [] = Nothing
findInput (InputFile f :: fs) = Just f
findInput (_ :: fs) = findInput fs

-- Options to be processed before type checking
preOptions : {auto c : Ref Ctxt Defs} ->
             List CLOpt -> Core FC ()
preOptions [] = pure ()
preOptions (Quiet :: opts)
    = do setSession (record { quiet = True } !getSession)
         preOptions opts
preOptions (NoPrelude :: opts)
    = do setSession (record { noprelude = True } !getSession)
         preOptions opts
preOptions (_ :: opts) = preOptions opts

-- Options to be processed after type checking. Returns whether execution
-- should continue (i.e., whether to start a REPL)
postOptions : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState FC)} ->
              {auto s : Ref Syn SyntaxInfo} ->
              List CLOpt -> Core FC Bool
postOptions [] = pure True
postOptions (ExecFn str :: rest) 
    = do execExp (PRef (MkFC "(script)" (0, 0) (0, 0)) (UN str))
         postOptions rest
         pure False
postOptions (CheckOnly :: rest) 
    = do postOptions rest
         pure False
postOptions (_ :: rest) = postOptions rest

-- Add extra library directories from the "BLODWEN_PATH"
-- environment variable
updatePaths : {auto c : Ref Ctxt Defs} ->
              Core annot ()
updatePaths
    = do setPrefix bprefix
         defs <- get Ctxt
         bpath <- coreLift $ getEnv "BLODWEN_PATH"
         case bpath of
              Just path => do traverse addExtraDir (map trim (split (==':') path))
                              pure ()
              Nothing => pure ()
         bdata <- coreLift $ getEnv "BLODWEN_DATA"
         case bdata of
              Just path => do traverse addDataDir (map trim (split (==':') path))
                              pure ()
              Nothing => pure ()
         -- BLODWEN_PATH goes first so that it overrides this if there's
         -- any conflicts. In particular, that means that setting BLODWEN_PATH
         -- for the tests means they test the local version not the installed
         -- version
         addExtraDir (dir_prefix (dirs (options defs)) ++ "/blodwen/prelude")
         addDataDir (dir_prefix (dirs (options defs)) ++ "/blodwen/support")

updateREPLOpts : {auto c : Ref ROpts REPLOpts} ->
                 Core annot ()
updateREPLOpts
    = do opts <- get ROpts
         ed <- coreLift $ getEnv "EDITOR"
         case ed of
              Just e => put ROpts (record { editor = e } opts)
              Nothing => pure ()

stMain : List CLOpt -> Core FC ()
stMain opts
    = do c <- newRef Ctxt initCtxt
         addPrimitives
         preOptions opts
         updatePaths

         let fname = findInput opts

         u <- newRef UST initUState
         s <- newRef Syn initSyntax
         o <- newRef ROpts (REPL.defaultOpts fname)

         updateREPLOpts
         case fname of
              Nothing => readPrelude
              Just f => updateErrorLine !(buildAll f)

         doRepl <- postOptions opts
         when doRepl $ 
              do putStrLnQ "Welcome to Blodwen. Good luck."
                 repl {c} {u}

-- Run any options (such as --version or --help) which imply printing a
-- message then exiting. Returns wheter the program should continue
quitOpts : List CLOpt -> IO Bool
quitOpts [] = pure True
quitOpts (Version :: _) 
    = do putStrLn versionMsg
         pure False
quitOpts (Help :: _)
    = do putStrLn usage
         pure False
quitOpts (_ :: opts) = quitOpts opts

main : IO ()
main = do Right opts <- getOpts
             | Left err =>
                    do putStrLn err
                       putStrLn usage
          continue <- quitOpts opts
          if continue
             then
                coreRun (stMain opts)
                     (\err : Error _ => putStrLn ("Uncaught error: " ++ show err))
                     (\res => pure ())
             else pure ()

