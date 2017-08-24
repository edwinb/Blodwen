-- Support for processing a file containing Raw TT definitions
-- (i.e. fully elaborated core)

module Core.ProcessTT

import Core.TT
import Core.Normalise
import Core.Typecheck
import Core.Unify
import Core.Context
import Core.RawContext

import Parser.Raw

import Control.Catchable
import Control.Monad.StateE
import Interfaces.FileIO

%default covering

using (FileIO m)
  processDecls : List RawDecl -> CoreI () m [Ctxt ::: Defs] ()
  processDecls decls
      = do -- putStrLn "Parsed OK"
           -- putStrLn (showSep "\n" (map show decls))
           xs <- traverse (\x => addDecl () x) decls
           pure ()

  export
  runMain : CoreI () m [Ctxt ::: Defs] ()
  runMain
      = case runParser "main" raw of
             Left err => printLn "Can't happen, error parsing 'main'"
             Right raw => do
               (ptm, pty) <- infer () [] raw
               putStr "Evaluating main: "
               gam <- getCtxt
               printLn (normalise gam [] ptm) 

  export
  process : String -> CoreI () m [Ctxt ::: Defs] ()
  process file
      = do Right res <- readFile file
                 | Left err => putStrLn ("File error: " ++ show err)
           case runParser res prog of
                Left err => putStrLn ("Parse error: " ++ show err)
                Right decls => 
                     catch (processDecls decls)
                           (\err => printLn err)

