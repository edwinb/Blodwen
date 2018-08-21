module Idris.SetOptions

import Core.Context
import Core.Directory
import Core.Options
import Core.Unify

import Idris.CommandLine
import Idris.REPL
import Idris.Syntax

import System

-- TODO: Version numbers on dependencies
export
addPkgDir : {auto c : Ref Ctxt Defs} ->
            String -> Core annot ()
addPkgDir p
    = do defs <- get Ctxt
         addExtraDir (dir_prefix (dirs (options defs)) ++ dirSep ++ 
                             "blodwen" ++ dirSep ++ p)

-- Options to be processed before type checking
export
preOptions : {auto c : Ref Ctxt Defs} ->
             List CLOpt -> Core annot ()
preOptions [] = pure ()
preOptions (Quiet :: opts)
    = do setSession (record { quiet = True } !getSession)
         preOptions opts
preOptions (NoPrelude :: opts)
    = do setSession (record { noprelude = True } !getSession)
         preOptions opts
preOptions (SetCG e :: opts)
    = case getCG e of
           Just cg => do setCG cg
                         preOptions opts
           Nothing => 
              do coreLift $ putStrLn "No such code generator"
                 coreLift $ putStrLn $ "Code generators available: " ++
                                 showSep ", " (map fst availableCGs)
                 coreLift $ exit 1
preOptions (PkgPath p :: opts)
    = do addPkgDir p
         preOptions opts
preOptions (_ :: opts) = preOptions opts

-- Options to be processed after type checking. Returns whether execution
-- should continue (i.e., whether to start a REPL)
export
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


