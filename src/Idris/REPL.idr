module Idris.REPL

import Compiler.Scheme.Chez
import Compiler.Scheme.Chicken
import Compiler.Scheme.Racket
import Compiler.Common

import Core.AutoSearch
import Core.CaseTree
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
import Idris.IDEMode.CaseSplit
import Idris.IDEMode.Commands
import Idris.ModTree
import Idris.Parser
import Idris.Resugar
import public Idris.REPLCommon
import Idris.Syntax

import TTImp.CaseSplit
import TTImp.Elab
import TTImp.ExprSearch
import TTImp.GenerateDef
import TTImp.MakeLemma
import TTImp.TTImp
import TTImp.ProcessTTImp
import TTImp.Reflect

import Control.Catchable

import System

%default covering

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

impBracket : Bool -> String -> String
impBracket False str = str
impBracket True str = "{" ++ str ++ "}"

showName : Name -> Bool
showName (UN "_") = False
showName (MN "_" _) = False
showName _ = True

tidy : Name -> String
tidy (MN n _) = n
tidy n = show n

showEnv : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Defs -> Env Term vars -> Name -> Nat -> Term vars -> 
          Core FC (List (Name, String), String)
showEnv gam env fn (S args) (Bind x (Let c val ty) sc)
    = showEnv gam env fn args (subst val sc)
showEnv gam env fn (S args) (Bind x b sc)
    = do ity <- resugar env (normaliseHoles gam env (binderType b))
         let pre = if showName x
                      then showCount (multiplicity b) ++ 
                           impBracket (implicitBind b) (tidy x ++ " : " ++ show ity) ++ "\n"
                      else ""
         (envstr, ret) <- showEnv gam (b :: env) fn args sc
         pure ((x, pre) :: envstr, ret)
  where
    implicitBind : Binder (Term vars) -> Bool
    implicitBind (Pi _ Explicit _) = False
    implicitBind (Pi _ _ _) = True
    implicitBind (Lam _ Explicit _) = False
    implicitBind (Lam _ _ _) = True
    implicitBind _ = False
showEnv gam env fn args ty
    = do ity <- resugar env (normaliseHoles gam env ty)
         pure ([], "-------------------------------------\n" ++
                    nameRoot fn ++ " : " ++ show ity)

showHole : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           Defs -> Env Term vars -> Name -> Nat -> Term vars -> 
           Core FC String
showHole gam env fn args ty
    = do (envs, ret) <- showEnv gam env fn args ty
         pp <- getPPrint
         let envs' = if showImplicits pp 
                        then envs
                        else dropShadows envs
         pure (concat (map snd envs') ++ ret)
  where
    dropShadows : List (Name, a) -> List (Name, a)
    dropShadows [] = []
    dropShadows ((n, ty) :: ns)
        = if n `elem` map fst ns
             then dropShadows ns
             else (n, ty) :: dropShadows ns

displayType : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, GlobalDef) -> 
              Core FC String
displayType gam (n, def) 
    = maybe (do tm <- resugar [] (normaliseHoles gam [] (type def))
                pure (show n ++ " : " ++ show tm))
            (\num => showHole gam [] n num (type def))
            (isHole def)

getEnvTerm : List Name -> Env Term vars -> Term vars ->
             (vars' ** (Env Term vars', Term vars'))
getEnvTerm (n :: ns) env (Bind x b sc)
    = if n == x
         then getEnvTerm ns (b :: env) sc
         else (_ ** (env, Bind x b sc))
getEnvTerm _ env tm = (_ ** (env, tm))

displayClause : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                Defs -> (List Name, ClosedTerm, ClosedTerm) -> 
                Core FC String
displayClause gam (vs, lhs, rhs)
    = do let (_ ** (env, lhsenv)) = getEnvTerm vs [] lhs
         lhstm <- resugar env (normaliseHoles gam env lhsenv)
         let (_ ** (env, rhsenv)) = getEnvTerm vs [] rhs
         rhstm <- resugar env (normaliseHoles gam env rhsenv)
         pure (show lhstm ++ " = " ++ show rhstm)

displayPats : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, GlobalDef) -> 
              Core FC String
displayPats gam (n, def)
    = case definition def of
           PMDef _ _ _ _ pats
               => do ty <- displayType gam (n, def)
                     ps <- traverse (displayClause gam) pats
                     pure (ty ++ "\n" ++ showSep "\n" ps)
           _ => pure (show n ++ " is not a pattern matching definition")

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
         
anyAt : (FC -> Bool) -> FC -> a -> Bool
anyAt p loc y = p loc

printClause : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Nat -> ImpClause FC ->
              Core FC String
printClause i (PatClause _ lhsraw rhsraw)
    = do lhs <- pterm lhsraw
         rhs <- pterm rhsraw
         pure (pack (replicate i ' ') ++ show lhs ++ " = " ++ show rhs)
printClause i (WithClause _ lhsraw wvraw csraw)
    = do lhs <- pterm lhsraw
         wval <- pterm wvraw
         cs <- traverse (printClause (i + 2)) csraw
         pure (pack (replicate i ' ') ++ show lhs ++ " with (" ++ show wval ++ ")\n" ++
                 showSep "\n" cs)
printClause i (ImpossibleClause _ lhsraw)
    = do lhs <- pterm lhsraw
         pure (pack (replicate i ' ') ++ show lhs ++ " impossible")

processEdit : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState FC)} ->
              {auto s : Ref Syn SyntaxInfo} ->
              {auto m : Ref Meta (Metadata FC)} ->
              {auto o : Ref ROpts REPLOpts} ->
              EditCmd -> Core FC ()
processEdit (TypeAt line col name)
    = do gam <- get Ctxt
         let glob = lookupGlobalName name (gamma gam)
         res <- the (Core _ String) $ case glob of
                     [] => pure ""
                     ts => do tys <- traverse (displayType gam) ts
                              pure (showSep "\n" tys)
         Just (n, num, t) <- findTypeAt (\p, n => within (line-1, col-1) p)
            | Nothing => if res == ""
                            then throw (UndefinedName (MkFC "(interactive)" (0,0) (0,0)) name)
                            else printResult res
         if res == ""
            then printResult !(showHole gam [] n num t)
            else printResult (res ++ "\n\n" ++ "Locally:\n" ++ 
                                     !(showHole gam [] n num t))
processEdit (CaseSplit line col name)
    = do let find = if col > 0
                       then within (line-1, col-1)
                       else onLine (line-1)
         OK splits <- getSplits (anyAt find) name
             | SplitFail err => printError (show err)
         lines <- updateCase splits (line-1) (col-1)
         printResult $ showSep "\n" lines ++ "\n"
processEdit (AddClause line name)
    = do Just c <- getClause line name
             | Nothing => printError (show name ++ " not defined here")
         printResult c
processEdit (ExprSearch line name hints all)
    = do gam <- get Ctxt
         syn <- get Syn
         let brack = elemBy (\x, y => dropNS x == dropNS y) name (bracketholes syn)
         case lookupDefName name (gamma gam) of
              [(n, Hole locs _ _)] =>
                  do tms <- exprSearch replFC name []
                     gam <- get Ctxt
                     let restms = map (normaliseHoles gam []) tms
                     itms <- the (Core _ (List PTerm)) 
                               (traverse (\tm => 
                                           do let (_ ** (env, tm')) = dropLams locs [] tm
                                              resugar env tm') restms)
                     if all
                        then printResult $ showSep "\n" (map show itms)
                        else case itms of
                                  [] => printError "No search results"
                                  (x :: xs) => printResult 
                                                  (show (if brack 
                                                            then addBracket replFC x
                                                            else x))
              [] => printError $ "Unknown name " ++ show name
              _ => printError "Not a searchable hole"
  where
    dropLams : Nat -> Env Term vars -> Term vars -> 
               (vars' ** (Env Term vars', Term vars'))
    dropLams Z env tm = (_ ** (env, tm))
    dropLams (S k) env (Bind _ b sc) = dropLams k (b :: env) sc 
    dropLams _ env tm = (_ ** (env, tm))
processEdit (GenerateDef line name)
    = do gam <- get Ctxt
         Just (_, n', _, _) <- findTyDeclAt (\p, n => onLine line p)
             | Nothing => printError ("Can't find declaration for " ++ show name ++ " on line " ++ show line)
         case lookupDefExact n' (gamma gam) of
              Just None =>
                  catch 
                    (do Just (fc, cs) <- makeDef (\p, n => onLine line p) n'
                           | Nothing => processEdit (AddClause line name)
                        ls <- traverse (printClause (cast (snd (startPos fc)))) cs
                        printResult $ showSep "\n" ls)
                    (\err => printError $ "Can't find a definition for " ++ show n')
              Just _ => printError "Already defined"
              Nothing => printError $ "Can't find declaration for " ++ show name
processEdit (MakeLemma line name)
    = do gam <- get Ctxt
         case lookupDefTyName name (gamma gam) of
              [(n, Hole locs _ _, ty)] =>
                  do (lty, lapp) <- makeLemma replFC name locs ty
                     pty <- pterm lty
                     papp <- pterm lapp
                     opts <- get ROpts
                     case idemode opts of
                          REPL _ => printResult (show name ++ " : " ++ show pty ++ "\n" ++ 
                                                 show papp)
                          IDEMode i =>
                            send (SExpList [SymbolAtom "return", 
                                    SExpList [SymbolAtom "ok",
                                      SExpList [SymbolAtom "metavariable-lemma",
                                        SExpList [SymbolAtom "replace-metavariable",
                                                  StringAtom (show papp)],
                                        SExpList [SymbolAtom "definition-type",
                                                  StringAtom (show name ++ " : " ++ show pty)]]],
                                            toSExp i])
              _ => printError "Can't make lifted definition"
processEdit (MakeCase line name)
    = printError "Not implemented yet"

export
loadMainFile : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState FC)} ->
               {auto s : Ref Syn SyntaxInfo} ->
               {auto m : Ref Meta (Metadata FC)} ->
               {auto o : Ref ROpts REPLOpts} ->
               String -> Core FC ()
loadMainFile f
    = do resetContext
         updateErrorLine !(buildDeps f)
         Right res <- coreLift (readFile f)
            | Left err => setSource ""
         setSource res

-- Returns 'True' if the REPL should continue
export
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
                 pure True
  where
    nfun : REPLEval -> Defs -> Env Term vs -> Term vs -> Term vs
    nfun NormaliseAll = normaliseAll
    nfun _ = normalise
process (Check (PRef fc fn))
    = do defs <- get Ctxt
         case lookupGlobalName fn (gamma defs) of
              [] => throw (UndefinedName fc fn)
              ts => do tys <- traverse (displayType defs) ts
                       printResult (showSep "\n" tys)
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
process (PrintDef fn)
    = do defs <- get Ctxt
         case lookupGlobalName fn (gamma defs) of
              [] => throw (UndefinedName replFC fn)
              ts => do defs <- traverse (displayPats defs) ts
                       printResult (showSep "\n" defs)
                       pure True
process Reload
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => do coreLift $ putStrLn "No file loaded"
                            pure True
              Just f => do loadMainFile f
                           pure True
process (Load f)
    = do opts <- get ROpts
         put ROpts (record { mainfile = Just f } opts)
         -- Clear the context and load again
         loadMainFile f
         pure True
process (CD dir)
    = do setWorkingDir dir
         pure True
process Edit
    = do opts <- get ROpts
         case mainfile opts of
              Nothing => do coreLift $ putStrLn "No file loaded"
                            pure True
              Just f =>
                do let line = maybe "" (\i => " +" ++ show i) (errorLine opts)
                   coreLift $ system (editor opts ++ " " ++ f ++ line)
                   loadMainFile f
                   pure True
process (Compile ctm outfile)
    = do i <- newRef ImpST (initImpState {annot = FC})
         ttimp <- desugar AnyExpr [] (PApp replFC (PRef replFC (UN "unsafePerformIO")) ctm)
         (tm, _, ty) <- inferTerm elabTop False (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         ok <- compile !findCG tm outfile
         maybe (pure ())
               (\fname => iputStrLn (outfile ++ " written"))
               ok
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
    = do iputStrLn "Bye for now!"
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
                           pure True)

parseRepl : String -> Either ParseError REPLCmd
parseRepl inp
    = case fnameCmd [(":load", Load), (":l", Load), (":cd", CD)] inp of
           Nothing => runParser inp (do c <- command; eoi; pure c)
           Just cmd => Right cmd
  where
    -- a right load of hackery - we can't tokenise the filename using the
    -- ordinary parser. There's probably a better way...
    getLoad : Nat -> (String -> REPLCmd) -> String -> Maybe REPLCmd
    getLoad n cmd str = Just (cmd (trim (substr n (length str) str)))

    fnameCmd : List (String, String -> REPLCmd) -> String -> Maybe REPLCmd
    fnameCmd [] inp = Nothing
    fnameCmd ((pre, cmd) :: rest) inp
        = if isPrefixOf pre inp
             then getLoad (length pre) cmd inp
             else fnameCmd rest inp

export
interpret : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST (UState FC)} ->
            {auto s : Ref Syn SyntaxInfo} ->
            {auto m : Ref Meta (Metadata FC)} ->
            {auto o : Ref ROpts REPLOpts} ->
            String -> Core FC Bool
interpret inp
    = case parseRepl inp of
           Left err => do printError (show err)
                          pure True
           Right cmd => processCatch cmd

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
         end <- coreLift $ fEOF stdin
         if end
            then iputStrLn "Bye for now!"
            else if !(interpret inp)
                    then repl
                    else pure ()

  where
    prompt : REPLEval -> String
    prompt EvalTC = "[tc] "
    prompt NormaliseAll = ""
    prompt Execute = "[exec] "

