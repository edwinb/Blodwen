module Idris.ProcessIdr

import Core.Binary
import Core.Context
import Core.Directory
import Core.UnifyState

import TTImp.TTImp
import TTImp.ProcessTTImp

import Idris.Parser
import Idris.Syntax
import Idris.Desugar

import Control.Catchable
import Interfaces.FileIO

processDecl : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState FC)} ->
              {auto i : Ref ImpST (ImpState FC)} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Env Term vars -> NestedNames vars ->
              PDecl -> Core FC ()
processDecl env nest decl
    = do impdecls <- desugarDecl decl 
         traverse (ProcessTTImp.processDecl env nest) impdecls
         pure ()

processDecls : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState FC)} ->
               {auto i : Ref ImpST (ImpState FC)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               Env Term vars -> NestedNames vars ->
               List PDecl -> Core FC ()
processDecls env nest decls
    = do xs <- traverse (processDecl env nest) decls
         hs <- getHoleNames
         traverse addToSave hs
         pure ()

-- Process everything in the module; return the syntax information which
-- needs to be written to the TTC (e.g. exported infix operators)
processMod : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState FC)} ->
             Module -> Core FC SyntaxInfo
processMod mod
    = do i <- newRef ImpST (initImpState {annot = FC})
         s <- newRef Syn initSyntax
         setNS (moduleNS mod)
         -- read imports here
         -- Note: We should only import .ttc - assumption is that there's
         -- a phase before this which builds the dependency graph
         -- (also that we only build child dependencies if rebuilding
         -- changes the interface - will need to store a hash in .ttc!)
         processDecls [] (MkNested []) (decls mod)
         get Syn

export
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState FC)} ->
          FileName -> Core FC ()
process file
    = do Right res <- coreLift (readFile file)
               | Left err => coreLift (putStrLn ("File error: " ++ show err))
         case runParser res (prog file) of
              Left err => coreLift (putStrLn ("Parser error: " ++ show err))
              Right mod =>
                    catch (do syn <- processMod mod
                              writeToTTC syn (getTTCFileName file))
                          (\err => coreLift (printLn err))

