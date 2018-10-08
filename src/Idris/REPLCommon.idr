module Idris.REPLCommon

import public Idris.REPLOpts
import Idris.Syntax
import Idris.IDEMode.Commands

-- Output informational messages, unless quiet flag is set
export
iputStrLn : {auto o : Ref ROpts REPLOpts} ->
            String -> Core annot ()
iputStrLn msg
    = do opts <- get ROpts
         case idemode opts of
              REPL False => coreLift $ putStrLn msg
              REPL _ => pure ()
              IDEMode i =>
                send (SExpList [SymbolAtom "write-string", 
                                toSExp msg, toSExp i])

printWithStatus : {auto o : Ref ROpts REPLOpts} ->
                  String -> String -> Core annot ()
printWithStatus status msg
    = do opts <- get ROpts
         case idemode opts of
              REPL _ => coreLift $ putStrLn msg
              IDEMode i =>
                do let m = SExpList [SymbolAtom status, toSExp msg]
                   send (SExpList [SymbolAtom "return", m, toSExp i])

export
printResult : {auto o : Ref ROpts REPLOpts} ->
              String -> Core annot ()
printResult msg = printWithStatus "ok" msg

export
printError : {auto o : Ref ROpts REPLOpts} ->
             String -> Core annot ()
printError msg = printWithStatus "error" msg


