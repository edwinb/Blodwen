-- Support for processing a file containing TTImp definitions

module TTImp.ProcessTTImp

import Core.TT
import Core.Normalise
import Core.Typecheck
import Core.Unify
import Core.Context

import TTImp.Elab
import TTImp.ProcessData
import TTImp.ProcessDef
import TTImp.ProcessType
import TTImp.TTImp

import Parser.RawImp

import Control.Catchable
import Control.Monad.StateE
import Interfaces.FileIO

%default covering

using (FileIO m)
  processDecl : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState annot)} ->
                {auto i : Ref ImpST (ImpState annot)} ->
                ImpDecl annot -> 
                Core annot ()
  processDecl (IClaim loc ty) = processType [] ty
  processDecl (IDef loc n cs) = processDef [] loc n cs
  processDecl (IData loc d) = processData [] d
  processDecl (ImplicitNames loc ns) 
      = do traverse (\ x => addImp (fst x) (snd x)) ns
           pure ()
  processDecl (ILog lvl) = setLogLevel lvl

  export
  processDecls : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST (UState annot)} ->
                 List (ImpDecl annot) -> 
                 Core annot ()
  processDecls decls
      = do i <- newRef ImpST (initImpState {annot})
           xs <- traverse (\x => processDecl x) decls
           pure ()

  export
  process : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST (UState ())} ->
            String -> Core () ()
  process file
      = do Right res <- ioe_lift (readFile file)
                 | Left err => ioe_lift (putStrLn ("File error: " ++ show err))
           case runParser res prog of
                Left err => ioe_lift (putStrLn ("TTImp Parse error: " ++ show err))
                Right decls => 
                     catch (processDecls decls)
                           (\err => ioe_lift (printLn err))

