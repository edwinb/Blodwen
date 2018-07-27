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

%default covering

findInput : List CLOpt -> String
findInput [] = "Prelude.blod"
findInput (InputFile f :: fs) = f
findInput (_ :: fs) = findInput fs

-- Options to be processed before type checking
preOptions : {auto c : Ref Ctxt Defs} ->
             List CLOpt -> Core FC ()
preOptions [] = pure ()
preOptions (Quiet :: opts)
    = do setSession (record { quiet = True } !getSession)
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

stMain : List CLOpt -> Core FC ()
stMain opts
    = do c <- newRef Ctxt initCtxt
         addPrimitives
         preOptions opts

         let fname = findInput opts

         u <- newRef UST initUState
         s <- newRef Syn initSyntax
         o <- newRef ROpts defaultOpts

         case span (/= '.') fname of
              -- This is temporary, until we get module chasing and
              -- need for rebuild checking...
              (_, ".ttc") => do putStrLnQ "Processing as TTC"
                                readAsMain fname
                                dumpConstraints 0 True
              _ => do putStrLnQ "Processing as Idris"
                      buildAll fname
         putStrLnQ "Welcome to Blodwen. Good luck."

         doRepl <- postOptions opts
         when doRepl $ repl {c} {u}

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

