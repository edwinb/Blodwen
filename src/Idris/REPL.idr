module Idris.REPL

import Compiler.Scheme.Chez
import Compiler.Scheme.Chicken
import Compiler.Scheme.Racket
import Compiler.Common

import Core.AutoSearch
import Core.CompileExpr
import Core.Context
import Core.InitPrimitives
import Core.Metadata
import Core.Normalise
import Core.Options
import Core.TT
import Core.Unify

import Idris.Desugar
import Idris.Error
import Idris.ModTree
import Idris.Parser
import Idris.Resugar
import Idris.Syntax

import TTImp.CaseSplit
import TTImp.Elab
import TTImp.TTImp
import TTImp.ProcessTTImp

import Control.Catchable
import TTImp.Reflect

import System

%default covering

public export
record REPLOpts where
  constructor MkREPLOpts
  showTypes : Bool
  evalMode : REPLEval
  mainfile : Maybe String
  editor : String
  errorLine : Maybe Int

export
defaultOpts : Maybe String -> REPLOpts
defaultOpts fname = MkREPLOpts False NormaliseAll fname "vim" Nothing

export
data ROpts : Type where

replFC : FC
replFC = MkFC "(interactive)" (0, 0) (0, 0)

getFCLine : FC -> Int
getFCLine fc = fst (startPos fc)

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

showHole : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           Defs -> Env Term vars -> Name -> Nat -> Term vars -> Core FC ()
showHole gam env fn (S args) (Bind x (Pi c inf ty) sc)
    = do ity <- resugar env (normaliseHoles gam env ty)
         when (showName x) $
           coreLift $ putStrLn $
              showCount c ++ impBracket inf (tidy x ++ " : " ++ show ity)
         showHole gam (Pi c inf ty :: env) fn args sc
showHole gam env fn (S args) (Bind x (PVar c ty) sc)
    = do ity <- resugar env (normaliseHoles gam env ty)
         when (showName x) $
           coreLift $ putStrLn $
              showCount c ++ impBracket Explicit (tidy x ++ " : " ++ show ity)
         showHole gam (PVar c ty :: env) fn args sc
showHole gam env fn args (Bind x (Let c val ty) sc)
    = showHole gam env fn args (subst val sc)
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
setOpt (ShowNamespace t) 
    = do pp <- getPPrint
         setPPrint (record { fullNamespace = t } pp)
setOpt (ShowTypes t) 
    = do opts <- get ROpts
         put ROpts (record { showTypes = t } opts)
setOpt (EvalMode m) 
    = do opts <- get ROpts
         put ROpts (record { evalMode = m } opts)
setOpt (Editor e)
    = do opts <- get ROpts
         put ROpts (record { editor = e } opts)
setOpt (CG e)
    = case getCG e of
           Just cg => setCG cg
           Nothing => coreLift $ putStrLn "No such code generator available"

findCG : {auto c : Ref Ctxt Defs} -> Core FC (Codegen FC)
findCG 
    = do defs <- get Ctxt
         case codegen (session (options defs)) of
              Chez => pure codegenChez
              Chicken => pure codegenChicken
              Racket => pure codegenRacket

export
execExp : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState FC)} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref Meta (Metadata FC)} ->
          PTerm -> Core FC ()
execExp ctm
    = do i <- newRef ImpST (initImpState {annot = FC})
         ttimp <- desugar AnyExpr [] (PApp replFC (PRef replFC (UN "unsafePerformIO")) ctm)
         (tm, _, ty) <- inferTerm elabTop False (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         execute !findCG tm
         
resetContext : {auto u : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState FC)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref Meta (Metadata FC)} ->
               Core FC ()
resetContext
    = do defs <- get Ctxt
         put Ctxt (record { options = clearNames (options defs) } initCtxt)
         addPrimitives
         put UST initUState
         put Syn initSyntax
         put Meta initMetadata

export
updateErrorLine : {auto o : Ref ROpts REPLOpts} ->
                  List (Error FC) -> Core FC ()
updateErrorLine []
    = do opts <- get ROpts
         put ROpts (record { errorLine = Nothing } opts)
updateErrorLine (e :: es)
    = do opts <- get ROpts
         put ROpts (record { errorLine = map getFCLine (getAnnot e) } opts)

processEdit : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState FC)} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto m : Ref Meta (Metadata FC)} ->
              {auto o : Ref ROpts REPLOpts} ->
              EditCmd -> Core FC ()
processEdit (TypeAt line col name)
    = do gam <- get Ctxt
         Just (n, num, t) <- findTypeAt (within (line-1, col-1))
            | Nothing => case lookupGlobalName name (gamma gam) of
                              [] => throw (UndefinedName (MkFC "(interactive)" (0,0) (0,0)) name)
                              ts => do traverse (displayType gam) ts
                                       pure ()
         showHole gam [] n num t
processEdit (CaseSplit line col name)
    = do res <- getSplits (within (line-1, col-1)) name
         pure ()

-- Returns 'True' if the REPL should continue
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState FC)} ->
          {auto s : Ref Syn SyntaxInfo} ->
          {auto m : Ref Meta (Metadata FC)} ->
          {auto o : Ref ROpts REPLOpts} ->
          REPLCmd -> Core FC Bool
process (Eval itm)
    = do opts <- get ROpts
         case evalMode opts of
            Execute => do execExp itm; pure True
            _ => 
              do i <- newRef ImpST (initImpState {annot = FC})
                 ttimp <- desugar AnyExpr [] itm
                 (tm, _, ty) <- inferTerm elabTop False (UN "[input]") 
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
         (tm, _, ty) <- inferTerm elabTop False (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         gam <- get Ctxt
         itm <- resugar [] (normaliseHoles gam [] tm)
         ity <- resugar [] (normaliseHoles gam [] ty)
         coreLift (putStrLn (show itm ++ " : " ++ show ity))
         pure True
process Reload
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => do coreLift $ putStrLn "No file loaded"
                            pure True
              Just f =>
                do -- Clear the context and load again
                   resetContext
                   updateErrorLine !(buildDeps f)
                   pure True
process (Load f)
    = do opts <- get ROpts
         put ROpts (record { mainfile = Just f } opts)
         -- Clear the context and load again
         resetContext
         updateErrorLine !(buildDeps f)
         pure True
process Edit
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => do coreLift $ putStrLn "No file loaded"
                            pure True
              Just f =>
                do let line = maybe "" (\i => " +" ++ show i) (errorLine opts)
                   coreLift $ system (editor opts ++ " " ++ f ++ line)
                   resetContext
                   updateErrorLine !(buildDeps f)
                   pure True
process (Compile ctm outfile)
    = do i <- newRef ImpST (initImpState {annot = FC})
         ttimp <- desugar AnyExpr [] (PApp replFC (PRef replFC (UN "unsafePerformIO")) ctm)
         (tm, _, ty) <- inferTerm elabTop False (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         compile !findCG tm outfile
         pure True
process (Exec ctm)
    = do execExp ctm
         pure True
process (ProofSearch n)
    = do tm <- search replFC False 1000 [] n Nothing (UN "(interactive)")
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
process (Editing cmd)
    = do processEdit cmd
         pure True
process Quit 
    = do coreLift $ putStrLn "Bye for now!"
         pure False

processCatch : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState FC)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref Meta (Metadata FC)} ->
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
                           coreLift (putStrLn !(perror err))
                           opts <- get ROpts
                           pure True)

parseRepl : String -> Either ParseError REPLCmd
parseRepl inp
   = if isPrefixOf ":load" inp
        then getLoad 5 inp
        else if isPrefixOf ":l" inp
                then getLoad 2 inp
                else runParser inp (do c <- command; eoi; pure c)
  where
    -- a right load of hackery - we can't tokenise the filename using the
    -- ordinary parser. There's probably a better way...
    getLoad : Nat -> String -> Either ParseError REPLCmd
    getLoad n str = Right (Load (trim (substr n (length str) str)))

export
repl : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST (UState FC)} ->
       {auto s : Ref Syn SyntaxInfo} ->
       {auto m : Ref Meta (Metadata FC)} ->
       {auto o : Ref ROpts REPLOpts} ->
       Core FC ()
repl
    = do ns <- getNS
         opts <- get ROpts
         coreLift (putStr (prompt (evalMode opts) ++ showSep "." (reverse ns) ++ "> "))
         inp <- coreLift getLine
         case parseRepl inp of
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

