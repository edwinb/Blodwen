module Main

import Core.TT
import Core.Normalise
import Core.Typecheck
import Core.Unify
import Core.Context
import Core.ProcessTT
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
  tryTTImp : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState ())} ->
             Core () ()
  tryTTImp
      = do ioe_lift (putStr "Blodwen> ")
           inp <- ioe_lift getLine
           case runParser inp expr of
                Left err => do ioe_lift (printLn err)
                               tryTTImp
                Right ttimp =>
                    do -- putStrLn $ "Parsed okay: " ++ show ttimp
                       (tm, ty) <- inferTerm [] PATTERN InExpr ttimp 
--                        putStrLn (show tm ++ " : " ++ show ty)
                       gam <- getCtxt
                       ioe_lift (putStrLn (show (normalise gam [] tm) ++ " : " ++
                                           show (normalise gam [] ty)))
                       tryTTImp

  usageMsg : Core () ()
  usageMsg = ioe_lift $ putStrLn "Usage: blodwen [source file]"

  stMain : Core () ()
  stMain 
      = do c <- newRef Ctxt initCtxt
           [_, fname] <- ioe_lift getArgs | _ => usageMsg
           ioe_lift $ putStrLn $ "Loading " ++ fname
           u <- newRef UST initUState
           case span (/= '.') fname of
                (_, ".tt") => do ioe_lift $ putStrLn "Processing as TT"
                                 ProcessTT.process fname
                _ => do ioe_lift $ putStrLn "Processing as TTImp"
                        ProcessTTImp.process fname
           tryTTImp {c} {u}

main : IO ()
main = do putStrLn "Welcome to Blodwen. Good luck."
          ioe_run stMain
               (\err : Error () => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())
