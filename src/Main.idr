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
      = do coreLift (putStr "Blodwen> ")
           inp <- coreLift getLine
           case runParser inp expr of
                Left err => do coreLift (printLn err)
                               tryTTImp
                Right ttimp =>
                    do -- putStrLn $ "Parsed okay: " ++ show ttimp
                       i <- newRef ImpST (initImpState {annot = ()})
                       (tm, ty) <- inferTerm elabTop (UN "[input]") 
                                             [] (MkNested []) NONE InExpr ttimp 
--                        putStrLn (show tm ++ " : " ++ show ty)
                       gam <- getCtxt
                       coreLift (putStrLn (show (normalise gam [] tm) ++ " : " ++
                                           show (normalise gam [] ty)))
                       tryTTImp

  usageMsg : Core () ()
  usageMsg = coreLift $ putStrLn "Usage: blodwen [source file]"

  stMain : Core () ()
  stMain 
      = do c <- newRef Ctxt initCtxt
           [_, fname] <- coreLift getArgs | _ => usageMsg
           coreLift $ putStrLn $ "Loading " ++ fname
           u <- newRef UST initUState
           case span (/= '.') fname of
                (_, ".tt") => do coreLift $ putStrLn "Processing as TT"
                                 ProcessTT.process fname
                _ => do coreLift $ putStrLn "Processing as TTImp"
                        ProcessTTImp.process fname
           tryTTImp {c} {u}

main : IO ()
main = do putStrLn "Welcome to Blodwen. Good luck."
          coreRun stMain
               (\err : Error () => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())
