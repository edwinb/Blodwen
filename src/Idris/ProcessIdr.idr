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
              PDecl -> Core FC ()
processDecl decl
    = do impdecls <- desugarDecl decl 
         traverse (ProcessTTImp.processDecl [] (MkNested [])) impdecls
         pure ()

processDecls : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState FC)} ->
               {auto i : Ref ImpST (ImpState FC)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               List PDecl -> Core FC ()
processDecls decls
    = do xs <- traverse processDecl decls
         hs <- getHoleNames
         traverse addToSave hs
         pure ()

-- Process everything in the module; return the syntax information which
-- needs to be written to the TTC (e.g. exported infix operators)
processMod : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState FC)} ->
             {auto s : Ref Syn SyntaxInfo} ->
             Module -> Core FC ()
processMod mod
    = do i <- newRef ImpST (initImpState {annot = FC})
         setNS (moduleNS mod)
         -- read imports here
         -- Note: We should only import .ttc - assumption is that there's
         -- a phase before this which builds the dependency graph
         -- (also that we only build child dependencies if rebuilding
         -- changes the interface - will need to store a hash in .ttc!)
         processDecls (decls mod)

export
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState FC)} ->
          {auto s : Ref Syn SyntaxInfo} ->
          FileName -> Core FC ()
process file
    = do Right res <- coreLift (readFile file)
               | Left err => coreLift (putStrLn ("File error: " ++ show err))
         case runParser res (prog file) of
              Left err => coreLift (putStrLn ("Parser error: " ++ show err))
              Right mod =>
                    catch (do processMod mod
                              writeToTTC !(get Syn) (getTTCFileName file))
                          (\err => coreLift (printLn err))

