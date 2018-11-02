-- Support for processing a file containing TTImp definitions

module TTImp.ProcessTTImp

import Core.Binary
import Core.Context
import Core.Metadata
import Core.Normalise
import Core.Reflect
import Core.TT
import Core.Typecheck
import Core.Unify

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
              {auto m : Ref Meta (Metadata annot)} ->
              (Reflect annot, Reify annot) =>
              (incase : Bool) ->
              Env Term vars ->
              NestedNames vars ->
              ImpDecl annot -> 
              Core annot ()
processDecl incase env nest (IClaim loc r vis fnopts ty) 
    = processType (\c, u, i, m => processDecl {c} {u} {i} {m})
                  env nest r vis fnopts ty
processDecl incase env nest (IDef loc n cs) 
    = processDef (\c, u, i, m => processDecl {c} {u} {i} {m})
                 incase env nest loc n cs
processDecl incase env nest (IData loc vis d) 
    = processData (\c, u, i, m => processDecl {c} {u} {i} {m})
                  env nest vis d
processDecl incase env nest (INamespace loc ns ds)
    = do oldns <- getNS
         extendNS (reverse ns)
         traverse (processDecl False env nest) ds
         setNS oldns
processDecl incase env nest (IReflect loc tm)
    = processReflect loc (\c, u, i, m => processDecl {c} {u} {i} {m})
                     env nest tm
processDecl incase env nest (ImplicitNames loc ns) 
    = do traverse (\ x => addImp (fst x) (snd x)) ns
         pure ()
processDecl incase env nest (IHint loc n Nothing) = addGlobalHint loc True n
processDecl incase env nest (IHint loc n (Just ty)) = addHintFor loc ty n True
processDecl incase env nest (IPragma p) = p env nest
processDecl incase env nest (ILog lvl) = setLogLevel lvl

export
processDecls : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState annot)} ->
               {auto m : Ref Meta (Metadata annot)} ->
               (Reflect annot, Reify annot) =>
               Env Term vars -> NestedNames vars ->
               List (ImpDecl annot) -> 
               Core annot ()
processDecls env nest decls
    = do i <- newRef ImpST (initImpState {annot})
         traverse (processDecl False env nest) decls
         dumpConstraints 0 True
         hs <- getHoleNames
         traverse addToSave hs
         pure ()

export
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState ())} ->
          {auto m : Ref Meta (Metadata ())} ->
          String -> Core () Bool
process file
    = do Right res <- coreLift (readFile file)
               | Left err => do coreLift (putStrLn ("File error: " ++ show err))
                                pure False
         case runParser res (do p <- prog; eoi; pure p) of
              Left err => do coreLift (putStrLn ("TTImp Parse error: " ++ show err))
                             pure False
              Right decls => 
                   catch (do processDecls [] (MkNested []) decls
                             pure True)
                         (\err => do coreLift (printLn err)
                                     pure False)

export
elabTop : (Reflect annot, Reify annot) => Elaborator annot
elabTop = \c, u, i, m => processDecl {c} {u} {i} {m}
