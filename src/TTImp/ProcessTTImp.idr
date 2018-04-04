-- Support for processing a file containing TTImp definitions

module TTImp.ProcessTTImp

import Core.Binary
import Core.TT
import Core.Normalise
import Core.Typecheck
import Core.Unify
import Core.Reflect
import Core.Context

import TTImp.Elab
import TTImp.ProcessData
import TTImp.ProcessDef
import TTImp.ProcessType
import TTImp.RunElab
import TTImp.TTImp

import Parser.RawImp

import Control.Catchable
import Control.Monad.StateE
import Interfaces.FileIO

%default covering

-- Need to propagate the top level elaborator 'processDecl' throughout
-- the rest of the elaborator, since otherwise we'd need cyclic modules
-- (that is, TTImp.Elab needs to call processDecl for nested constructs)
export
processDecl : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              (Reflect annot, Reify annot) =>
              Env Term vars ->
              NestedNames vars ->
              ImpDecl annot -> 
              Core annot ()
processDecl env nest (IClaim loc vis fnopts ty) 
    = processType (\c, u, i => processDecl {c} {u} {i})
                  env nest vis fnopts ty
processDecl env nest (IDef loc n cs) 
    = processDef (\c, u, i => processDecl {c} {u} {i})
                 env nest loc n cs
processDecl env nest (IData loc vis d) 
    = processData (\c, u, i => processDecl {c} {u} {i})
                  env nest vis d
processDecl env nest (INamespace loc ns ds)
    = do oldns <- getNS
         extendNS (reverse ns)
         traverse (processDecl env nest) ds
         setNS oldns
processDecl env nest (IReflect loc tm)
    = processReflect loc (\c, u, i => processDecl {c} {u} {i})
                     env nest tm
processDecl env nest (ImplicitNames loc ns) 
    = do traverse (\ x => addImp (fst x) (snd x)) ns
         pure ()
processDecl env nest (IHint loc n Nothing) = addGlobalHint loc n
processDecl env nest (IHint loc n (Just ty)) = addHintFor loc ty n
processDecl {c} env nest (IPragma p) = p c
processDecl env nest (ILog lvl) = setLogLevel lvl

export
processDecls : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState annot)} ->
               (Reflect annot, Reify annot) =>
               Env Term vars -> NestedNames vars ->
               List (ImpDecl annot) -> 
               Core annot ()
processDecls env nest decls
    = do i <- newRef ImpST (initImpState {annot})
         traverse (processDecl env nest) decls
         dumpConstraints 0 True
         hs <- getHoleNames
         traverse addToSave hs
         pure ()

export
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState ())} ->
          String -> Core () ()
process file
    = do Right res <- coreLift (readFile file)
               | Left err => coreLift (putStrLn ("File error: " ++ show err))
         case runParser res (do p <- prog; eoi; pure p) of
              Left err => coreLift (putStrLn ("TTImp Parse error: " ++ show err))
              Right decls => 
                   catch (processDecls [] (MkNested []) decls)
                         (\err => coreLift (printLn err))

export
elabTop : (Reflect annot, Reify annot) => Elaborator annot
elabTop = \c, u, i => processDecl {c} {u} {i}
