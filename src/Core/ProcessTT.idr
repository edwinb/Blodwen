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
  processDecls : {auto c : Ref Ctxt Defs} -> List RawDecl -> Core () ()
  processDecls decls
      = do -- putStrLn "Parsed OK"
           -- putStrLn (showSep "\n" (map show decls))
           xs <- traverse (\x => addDecl () x) decls
           pure ()

  export
  runMain : {auto c : Ref Ctxt Defs} -> Core () ()
  runMain
      = case runParser "main" raw of
             Left err => ioe_lift (printLn "Can't happen, error parsing 'main'")
             Right raw => do
               (ptm, pty) <- infer () [] raw
               ioe_lift (putStr "Evaluating main: ")
               gam <- getCtxt
               ioe_lift (printLn (normalise gam [] ptm))

  export
  process : {auto c : Ref Ctxt Defs} ->
            String -> Core () ()
  process file
      = do Right res <- ioe_lift (readFile file)
                 | Left err => ioe_lift (putStrLn ("File error: " ++ show err))
           case runParser res prog of
                Left err => ioe_lift (putStrLn ("TT Parse error: " ++ show err))
                Right decls => 
                     catch (processDecls decls)
                           (\err => ioe_lift (printLn err))

