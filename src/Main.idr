module Main

import Core.TT
import Core.Normalise
import Core.Typecheck
import Core.Context
import Core.RawContext
import TTImp.TTImp
import TTImp.Elab

import Parser.RawImp
import Parser.Raw

import Control.ST
import Control.IOExcept
import Interfaces.FileIO
import Interfaces.SystemIO

%default covering

using (CtxtManage m, FileIO m)
  processDecls : (ctxt : Var) -> List RawDecl -> ST m () [ctxt ::: Defs]
  processDecls ctxt decls
      = do -- putStrLn "Parsed OK"
           -- putStrLn (showSep "\n" (map show decls))
           xs <- mapST (addDecl ctxt) decls
           pure ()

  process : (ctxt : Var) -> String -> ST m () [ctxt ::: Defs]
  process ctxt file
      = do Right res <- readFile file
                 | Left err => putStrLn ("File error: " ++ show err)
           case runParser res prog of
                Left err => putStrLn ("Parse error: " ++ show err)
                Right decls => 
                     catch (processDecls ctxt decls)
                           (\err => printLn err)

  runMain : (ctxt : Var) -> ST m () [ctxt ::: Defs]
  runMain ctxt
      = case runParser "main" raw of
             Left err => printLn "Can't happen, error parsing 'main'"
             Right raw => do
               (ptm, pty) <- infer ctxt [] raw
               putStr "Evaluating main: "
               gam <- getCtxt ctxt
               printLn (normalise gam [] ptm) 

  tryTTImp : (ctxt : Var) -> ST m () [ctxt ::: Defs]
  tryTTImp ctxt
      = do putStr "Blodwen> "
           inp <- getStr
           case runParser inp expr of
                Left err => do printLn err
                               tryTTImp ctxt
                Right ttimp =>
                    do putStrLn $ "Parsed okay: " ++ show ttimp
                       tryTTImp ctxt

  usageMsg : ST m () []
  usageMsg = putStrLn "Usage: blodwen [source file]"

  stMain : SystemIO m => ST m () []
  stMain 
      = do ctxt <- newCtxt
           [_, fname] <- getArgs | _ => do usageMsg; deleteCtxt ctxt
           putStrLn $ "Loading " ++ fname
           process ctxt fname
           tryTTImp ctxt
           deleteCtxt ctxt

main : IO ()
main = do putStrLn "Welcome to Blodwen. Good luck."
          ioe_run (run stMain)
               (\err : Error => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())
