module Idris.REPL

import Compiler.Chez

import Core.AutoSearch
import Core.CompileExpr
import Core.Context
import Core.Normalise
import Core.Options
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
import TTImp.Reflect

%default covering

public export
record REPLOpts where
  constructor MkREPLOpts
  showTypes : Bool
  evalMode : REPLEval

export
defaultOpts : REPLOpts
defaultOpts = MkREPLOpts False NormaliseAll

export
data ROpts : Type where

replFC : FC
replFC = MkFC "(interactive)" (0, 0) (0, 0)

showInfo : (Name, GlobalDef) -> Core annot ()
showInfo (n, d) 
    = do coreLift $ putStrLn (show n ++ " ==> " ++ show (definition d))
         case compexpr d of
              Nothing => pure ()
              Just expr => coreLift $ putStrLn ("Compiled: " ++ show expr)
         coreLift $ putStrLn ("Refers to: " ++ show (refersTo d))

isHole : GlobalDef -> Maybe Nat
isHole def
    = case definition def of
           Hole locs _ _ => Just locs
           _ => Nothing

showHole : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           Defs -> Env Term vars -> Name -> Nat -> Term vars -> Core FC ()
showHole gam env fn (S args) (Bind x (Pi c inf ty) sc)
    = do ity <- resugar env (normaliseHoles gam env ty)
         when (showName x) $
           coreLift $ putStrLn $
              showCount c ++ impBracket inf (tidy x ++ " : " ++ show ity)
         showHole gam (Pi c inf ty :: env) fn args sc
  where
    showCount : RigCount -> String
    showCount Rig0 = " 0 "
    showCount Rig1 = " 1 "
    showCount RigW = "   "

    impBracket : PiInfo -> String -> String
    impBracket Explicit str = str
    impBracket _ str = "{" ++ str ++ "}"

    showName : Name -> Bool
    showName (UN "_") = False
    showName (MN "_" _) = False
    showName _ = True

    tidy : Name -> String
    tidy (MN n _) = n
    tidy n = show n

showHole gam env fn args ty
    = do coreLift $ putStrLn "-------------------------------------"
         ity <- resugar env (normaliseHoles gam env ty)
         coreLift $ putStrLn $ nameRoot fn ++ " : " ++ show ity

displayType : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, GlobalDef) -> Core FC ()
displayType gam (n, def) 
    = maybe (do tm <- resugar [] (normaliseHoles gam [] (type def))
                coreLift $ putStrLn $ show n ++ " : " ++ show tm)
            (\num => showHole gam [] n num (type def))
            (isHole def)

setOpt : {auto c : Ref Ctxt Defs} ->
         {auto o : Ref ROpts REPLOpts} ->
         REPLOpt -> Core FC ()
setOpt (ShowImplicits t) 
    = do pp <- getPPrint
         setPPrint (record { showImplicits = t } pp)
setOpt (ShowTypes t) 
    = do opts <- get ROpts
         put ROpts (record { showTypes = t } opts)
setOpt (EvalMode m) 
    = do opts <- get ROpts
         put ROpts (record { evalMode = m } opts)

export
execExp : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState FC)} ->
          {auto s : Ref Syn SyntaxInfo} ->
          PTerm -> Core FC ()
execExp ctm
    = do i <- newRef ImpST (initImpState {annot = FC})
         ttimp <- desugar AnyExpr [] (PApp replFC (PRef replFC (UN "unsafePerformIO")) ctm)
         (tm, _, ty) <- inferTerm elabTop (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         executeExpr tm
          
-- Returns 'True' if the REPL should continue
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState FC)} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto o : Ref ROpts REPLOpts} ->
          REPLCmd -> Core FC Bool
process (Eval itm)
    = do opts <- get ROpts
         case evalMode opts of
            Execute => do execExp itm; pure True
            _ => 
              do i <- newRef ImpST (initImpState {annot = FC})
                 ttimp <- desugar AnyExpr [] itm
                 (tm, _, ty) <- inferTerm elabTop (UN "[input]") 
                                       Env.Nil (MkNested []) NONE InExpr ttimp 
                 gam <- get Ctxt
                 opts <- get ROpts
                 let norm = nfun (evalMode opts)
                 itm <- resugar [] (norm gam [] tm)
                 if showTypes opts
                    then do ity <- resugar [] (norm gam [] ty)
                            coreLift (putStrLn (show itm ++ " : " ++ show ity))
                    else coreLift (putStrLn (show itm))
                 dumpConstraints 0 True
                 pure True
  where
    nfun : REPLEval -> Defs -> Env Term vs -> Term vs -> Term vs
    nfun NormaliseAll = normaliseAll
    nfun _ = normalise
process (Check (PRef fc fn))
    = do defs <- get Ctxt
         case lookupGlobalName fn (gamma defs) of
              [] => throw (UndefinedName fc fn)
              ts => do traverse (displayType defs) ts
                       pure True
process (Check itm)
    = do i <- newRef ImpST (initImpState {annot = FC})
         ttimp <- desugar AnyExpr [] itm
         (tm, _, ty) <- inferTerm elabTop (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         gam <- get Ctxt
         itm <- resugar [] (normaliseHoles gam [] tm)
         ity <- resugar [] (normaliseHoles gam [] ty)
         coreLift (putStrLn (show itm ++ " : " ++ show ity))
         pure True
process (Compile ctm outfile)
    = do i <- newRef ImpST (initImpState {annot = FC})
         ttimp <- desugar AnyExpr [] (PApp replFC (PRef replFC (UN "unsafePerformIO")) ctm)
         (tm, _, ty) <- inferTerm elabTop (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         compileExpr tm (outfile ++ ".ss")
         coreLift $ putStrLn (outfile ++ ".ss written")
         pure True
process (Exec ctm)
    = do execExp ctm
         pure True
process (ProofSearch n)
    = do tm <- search replFC False 1000 [] n (UN "(interactive)")
         gam <- get Ctxt
         itm <- resugar [] (normaliseHoles gam [] tm)
         coreLift (putStrLn (show itm))
         dumpConstraints 0 True
         pure True
process (DebugInfo n)
    = do gam <- get Ctxt
         traverse showInfo (lookupGlobalName n (gamma gam))
         pure True
process (SetOpt opt)
    = do setOpt opt
         pure True
process Quit 
    = do coreLift $ putStrLn "Bye for now!"
         pure False

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState FC)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto o : Ref ROpts REPLOpts} ->
               REPLCmd -> Core FC Bool
processCatch cmd
    = do c' <- get Ctxt
         u' <- get UST
         s' <- get Syn
         o' <- get ROpts
         catch (process cmd) 
               (\err => do put Ctxt c'
                           put UST u'
                           put Syn s'
                           put ROpts o'
                           coreLift (putStrLn (show err))
                           pure True)

export
repl : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST (UState FC)} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto o : Ref ROpts REPLOpts} ->
       Core FC ()
repl
    = do ns <- getNS
         opts <- get ROpts
         coreLift (putStr (prompt (evalMode opts) ++ showSep "." (reverse ns) ++ "> "))
         inp <- coreLift getLine
         case runParser inp (do c <- command; eoi; pure c) of
              Left err => do coreLift (printLn err)
                             repl
              Right cmd =>
                  do if !(processCatch cmd)
                        then repl
                        else pure ()
  where
    prompt : REPLEval -> String
    prompt EvalTC = "[tc] "
    prompt NormaliseAll = ""
    prompt Execute = "[exec] "

