module Main

import Core.TT
import Core.Normalise
import Core.Typecheck
import Core.Unify
import Core.Context
import Core.RawContext
import TTImp.TTImp
import TTImp.Elab

import Parser.RawImp
import Parser.Raw

import Control.Catchable
import Control.Monad.StateE
import Interfaces.FileIO
import Interfaces.SystemIO

%default covering

using (FileIO m)
  processDecls : List RawDecl -> CoreI () m [Ctxt ::: Defs] ()
  processDecls decls
      = do -- putStrLn "Parsed OK"
           -- putStrLn (showSep "\n" (map show decls))
           xs <- traverse (\x => addDecl () x) decls
           pure ()

  process : String -> CoreI () m [Ctxt ::: Defs] ()
  process file
      = do Right res <- readFile file
                 | Left err => putStrLn ("File error: " ++ show err)
           case runParser res prog of
                Left err => putStrLn ("Parse error: " ++ show err)
                Right decls => 
                     catch (processDecls decls)
                           (\err => printLn err)

  runMain : CoreI () m [Ctxt ::: Defs] ()
  runMain
      = case runParser "main" raw of
             Left err => printLn "Can't happen, error parsing 'main'"
             Right raw => do
               (ptm, pty) <- infer () [] raw
               putStr "Evaluating main: "
               gam <- getCtxt
               printLn (normalise gam [] ptm) 

  tryTTImp : CoreI () m [Ctxt ::: Defs, UST ::: UState ()] ()
  tryTTImp
      = do putStr "Blodwen> "
           inp <- getStr
           case runParser inp expr of
                Left err => do printLn err
                               tryTTImp
                Right ttimp =>
                    do -- putStrLn $ "Parsed okay: " ++ show ttimp
                       (tm, ty) <- inferTerm [] (PI False) ttimp 
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
           process fname
           ustate <- setupUnify
           tryTTImp
           doneUnify
           deleteCtxt

main : IO ()
main = do putStrLn "Welcome to Blodwen. Good luck."
          ioe_run (runSTE stMain [])
               (\err : Error () => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())
