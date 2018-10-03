module Main

import Core.Binary
import Core.Context
import Core.Directory
import Core.InitPrimitives
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.ProcessTT
import Core.RawContext
import Core.Reflect
import Core.TT
import Core.Typecheck
import Core.Unify

import TTImp.Elab
import TTImp.ProcessTTImp
import TTImp.REPL
import TTImp.TTImp

import Parser.RawImp

usageMsg : Core () ()
usageMsg = coreLift $ putStrLn "Usage: ttimp [source file]"

stMain : Core () ()
stMain 
    = do c <- newRef Ctxt initCtxt
         addPrimitives

         [_, fname] <- coreLift getArgs | _ => usageMsg
         coreLift $ putStrLn $ "Loading " ++ fname
         u <- newRef UST initUState
         m <- newRef Meta initMetadata
         case span (/= '.') fname of
              (_, ".tt") => do coreLift $ putStrLn "Processing as TT"
                               ProcessTT.process fname
                               makeBuildDirectory (pathToNS fname)
                               writeToTTC () !(getTTCFileName fname ".ttc")
              (_, ".ttc") => do coreLift $ putStrLn "Processing as TTC"
                                readFromTTC {extra = ()} () True fname [] []
                                dumpConstraints 0 True
              _ => do coreLift $ putStrLn "Processing as TTImp"
                      ok <- ProcessTTImp.process fname
                      when ok $
                         do makeBuildDirectory (pathToNS fname)
                            writeToTTC () !(getTTCFileName fname ".ttc")
         repl {c} {u} {m}

main : IO ()
main = do putStrLn "Welcome to TTImp. Good luck."
          coreRun stMain
               (\err : Error () => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())
