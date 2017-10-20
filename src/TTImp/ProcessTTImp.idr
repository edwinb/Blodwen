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
  -- Need to propagate the top level elaborator 'processDecl' throughout
  -- the rest of the elaborator, since otherwise we'd need cyclic modules
  -- (that is, TTImp.Elab needs to call processDecl for nested constructs)
  processDecl : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState annot)} ->
                {auto i : Ref ImpST (ImpState annot)} ->
                Env Term vars ->
                ImpDecl annot -> 
                Core annot ()
  processDecl env (IClaim loc ty) 
      = processType (\c, u, i => processDecl {c} {u} {i})
                    env ty
  processDecl env (IDef loc n cs) 
      = processDef (\c, u, i => processDecl {c} {u} {i})
                   env loc n cs
  processDecl env (IData loc d) 
      = processData (\c, u, i => processDecl {c} {u} {i})
                    env d
  processDecl env (ImplicitNames loc ns) 
      = do traverse (\ x => addImp (fst x) (snd x)) ns
           pure ()
  processDecl env (ILog lvl) = setLogLevel lvl

  export
  processDecls : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST (UState annot)} ->
                 Env Term vars ->
                 List (ImpDecl annot) -> 
                 Core annot ()
  processDecls vars decls
      = do i <- newRef ImpST (initImpState {annot})
           xs <- traverse (processDecl vars) decls
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
                     catch (processDecls [] decls)
                           (\err => ioe_lift (printLn err))

  export
  elabTop : Elaborator annot
  elabTop = \c, u, i => processDecl {c} {u} {i}
