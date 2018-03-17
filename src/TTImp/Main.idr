module Main

import Core.Binary
import Core.TT
import Core.Normalise
import Core.Typecheck
import Core.Unify
import Core.Context
import Core.ProcessTT
import Core.RawContext
import Core.Directory
import Core.Options

import TTImp.Elab
import TTImp.ProcessTTImp
import TTImp.TTImp
import TTImp.REPL

import Parser.RawImp

usageMsg : Core () ()
usageMsg = coreLift $ putStrLn "Usage: ttimp [source file]"

stMain : Core () ()
stMain 
    = do c <- newRef Ctxt initCtxt
         [_, fname] <- coreLift getArgs | _ => usageMsg
         coreLift $ putStrLn $ "Loading " ++ fname
         u <- newRef UST initUState
         case span (/= '.') fname of
              (_, ".tt") => do coreLift $ putStrLn "Processing as TT"
                               ProcessTT.process fname
                               makeBuildDirectory (pathToNS fname)
                               writeToTTC () !(getTTCFileName fname)
              (_, ".ttc") => do coreLift $ putStrLn "Processing as TTC"
                                readFromTTC {extra = ()} fname [] []
                                dumpConstraints 0 True
              _ => do coreLift $ putStrLn "Processing as TTImp"
                      ProcessTTImp.process fname
                      makeBuildDirectory (pathToNS fname)
                      writeToTTC () !(getTTCFileName fname)
         repl {c} {u}

main : IO ()
main = do putStrLn "Welcome to TTImp. Good luck."
          coreRun stMain
               (\err : Error () => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())
