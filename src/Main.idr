module Main

import Core.TT
import Core.Normalise
import Core.Typecheck
import Core.Unify
import Core.Context
import Core.RawContext

import TTImp.Elab
import TTImp.ProcessTTImp
import TTImp.TTImp

import Parser.RawImp

import Control.Catchable
import Control.Monad.StateE
import Interfaces.FileIO
import Interfaces.SystemIO

using (FileIO m)
  tryTTImp : CoreI () m [Ctxt ::: Defs, UST ::: UState ()] ()
  tryTTImp
      = do putStr "Blodwen> "
           inp <- getStr
           case runParser inp expr of
                Left err => do printLn err
                               tryTTImp
                Right ttimp =>
                    do -- putStrLn $ "Parsed okay: " ++ show ttimp
                       (tm, ty) <- inferTerm [] PATTERN InExpr ttimp 
--                        putStrLn (show tm ++ " : " ++ show ty)
                       gam <- getCtxt
                       putStrLn (show (normalise gam [] tm) ++ " : " ++
                                 show (normalise gam [] ty))
                       tryTTImp

  usageMsg : Core () [] ()
  usageMsg = putStrLn "Usage: blodwen [source file]"

  stMain : SystemIO m => CoreI () m [] ()
  stMain 
      = do newCtxt
           [_, fname] <- getArgs | _ => do usageMsg; deleteCtxt
           putStrLn $ "Loading " ++ fname
           setupUnify
           process fname
           tryTTImp
           doneUnify
           deleteCtxt

main : IO ()
main = do putStrLn "Welcome to Blodwen. Good luck."
          ioe_run (runSTE stMain [])
               (\err : Error () => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())
