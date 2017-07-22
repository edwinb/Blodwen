module Main

import Core.TT
import Core.Evaluate
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

using (CtxtManage m, FileIO m)
  processDecls : (ctxt : Var) -> List RawDecl -> ST m () [ctxt ::: Defs]
  processDecls ctxt decls
      = do putStrLn "Parsed OK"
           putStrLn (showSep "\n" (map show decls))
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

  stMain : ST m () []
  stMain 
      = do ctxt <- newCtxt
           process ctxt "test.tt"
           case runParser "main" raw of
                Left err => deleteCtxt ctxt
                Right raw => do
                  (ptm, pty) <- infer ctxt [] raw
                  putStr "Evaluating main: "
                  gam <- getCtxt ctxt
                  printLn (normalise gam [] ptm) 
                  deleteCtxt ctxt

main : IO ()
main = do putStrLn "Welcome to Blodwen. Good luck."
          ioe_run (run stMain)
               (\err : Error => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())
