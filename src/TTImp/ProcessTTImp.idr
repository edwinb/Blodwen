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
  processDecl : ImpDecl annot -> 
                CoreI annot m [Ctxt ::: Defs, UST ::: UState annot,
                               ImpST ::: ImpState annot] ()
  processDecl (IClaim loc ty) = processType [] ty
  processDecl (IDef loc n cs) = processDef [] loc n cs
  processDecl (IData loc d) = processData [] d
  processDecl (ImplicitNames loc ns) 
      = do traverse (\ x => addImp (fst x) (snd x)) ns
           pure ()
  processDecl (ILog lvl) = setLogLevel lvl

  export
  processDecls : List (ImpDecl annot) -> 
                 CoreI annot m [Ctxt ::: Defs, UST ::: UState annot] ()
  processDecls decls
      = do setupImpState
           xs <- traverse (\x => processDecl x) decls
           deleteImpState
           pure ()

  export
  process : String -> CoreI () m [Ctxt ::: Defs, UST ::: UState ()] ()
  process file
      = do Right res <- readFile file
                 | Left err => putStrLn ("File error: " ++ show err)
           case runParser res prog of
                Left err => putStrLn ("TTImp Parse error: " ++ show err)
                Right decls => 
                     catch (processDecls decls)
                           (\err => printLn err)

