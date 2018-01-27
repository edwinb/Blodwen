module Main

import Core.Binary
import Core.Context
import Core.Core
import Core.Directory
import Core.Primitives
import Core.Unify

import Idris.Desugar
import Idris.Syntax
import Idris.Parser
import Idris.ProcessIdr
import Idris.REPL


import Data.Vect

usageMsg : Core FC ()
usageMsg = coreLift $ putStrLn "Usage: blodwen [source file]"

stMain : Core FC ()
stMain 
    = do c <- newRef Ctxt initCtxt
         addPrimitives

         [_, fname] <- coreLift getArgs | _ => usageMsg
         coreLift $ putStrLn $ "Loading " ++ fname
         u <- newRef UST initUState
         s <- newRef Syn initSyntax

         case span (/= '.') fname of
              (_, ".ttc") => do coreLift $ putStrLn "Processing as TTC"
                                syn <- readFromTTC {extra = SyntaxInfo} fname
                                dumpConstraints 0 True
                                put Syn syn
              _ => do coreLift $ putStrLn "Processing as Idris"
                      ProcessIdr.process fname
                      syn <- get Syn
                      writeToTTC syn (getTTCFileName fname)
         repl {c} {u}


main : IO ()
main = do putStrLn "Welcome to Blodwen. Good luck."
          coreRun stMain
               (\err : Error _ => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())

