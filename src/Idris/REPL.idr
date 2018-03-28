module Idris.REPL

import Core.AutoSearch
import Core.Context
import Core.Normalise
import Core.TT
import Core.Unify

import Idris.Desugar
import Idris.Parser
import Idris.Resugar
import Idris.Syntax

import TTImp.Elab
import TTImp.TTImp
import TTImp.ProcessTTImp

import Control.Catchable

%default covering

showInfo : (Name, Def) -> Core annot ()
showInfo (n, d) = coreLift $ putStrLn (show n ++ " ==> " ++ show d)

-- Returns 'True' if the REPL should continue
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState FC)} ->
          {auto s : Ref Syn SyntaxInfo} ->
          REPLCmd -> Core FC Bool
process (Eval itm)
    = do i <- newRef ImpST (initImpState {annot = FC})
         ttimp <- desugar itm
         (tm, ty) <- inferTerm elabTop (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         gam <- get Ctxt
         itm <- resugar [] (normalise gam [] tm)
         ity <- resugar [] (normalise gam [] ty)
         coreLift (putStrLn (show itm ++ " : " ++ show ity))
         pure True
process (Check itm)
    = do i <- newRef ImpST (initImpState {annot = FC})
         ttimp <- desugar itm
         (tm, ty) <- inferTerm elabTop (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         gam <- get Ctxt
         itm <- resugar [] (normaliseHoles gam [] tm)
         ity <- resugar [] (normaliseHoles gam [] ty)
         coreLift (putStrLn (show itm ++ " : " ++ show ity))
         pure True
process (ProofSearch n)
    = do tm <- search (MkFC "(interactive)" (0, 0) (0, 0)) 1000 n
         gam <- get Ctxt
         itm <- resugar [] (normaliseHoles gam [] tm)
         coreLift (putStrLn (show itm))
         dumpConstraints 0 True
         pure True
process (DebugInfo n)
    = do gam <- get Ctxt
         traverse showInfo (lookupDefName n (gamma gam))
         pure True
process Quit 
    = do coreLift $ putStrLn "Bye for now!"
         pure False

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState FC)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               REPLCmd -> Core FC Bool
processCatch cmd
    = catch (process cmd) (\err => do coreLift (putStrLn (show err))
                                      pure True)

export
repl : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST (UState FC)} ->
       {auto s : Ref Syn SyntaxInfo} ->
       Core FC ()
repl
    = do ns <- getNS
         coreLift (putStr (showSep "." (reverse ns) ++ "> "))
         inp <- coreLift getLine
         case runParser inp (do c <- command; eoi; pure c) of
              Left err => do coreLift (printLn err)
                             repl
              Right cmd =>
                  do if !(processCatch cmd)
                        then repl
                        else pure ()


