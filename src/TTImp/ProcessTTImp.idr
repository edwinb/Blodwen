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
  processDecl : ImpDecl annot -> CoreI annot m 
                                 [Ctxt ::: Defs, UST ::: UState annot] ()
  processDecl (IClaim loc ty) = processType [] ty
  processDecl (IDef loc n cs) = processDef [] loc n cs
  processDecl (IData loc d) = processData [] d

  export
  processDecls : List (ImpDecl annot) -> 
                 CoreI annot m [Ctxt ::: Defs, UST ::: UState annot] ()
  processDecls decls
      = do xs <- traverse (\x => processDecl x) decls
           pure ()

  export
  process : String -> CoreI () m [Ctxt ::: Defs, UST ::: UState ()] ()
  process file
      = do Right res <- readFile file
                 | Left err => putStrLn ("File error: " ++ show err)
           case runParser res prog of
                Left err => putStrLn ("Parse error: " ++ show err)
                Right decls => 
                     catch (processDecls decls)
                           (\err => printLn err)

