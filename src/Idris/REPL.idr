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
import TTImp.Reflect

%default covering

showInfo : (Name, Def) -> Core annot ()
showInfo (n, d) = coreLift $ putStrLn (show n ++ " ==> " ++ show d)

isHole : GlobalDef -> Bool
isHole def
    = case definition def of
           Hole _ _ => True
           _ => False

showHole : {auto c : Ref Ctxt Defs} ->
           {auto s : Ref Syn SyntaxInfo} ->
           Defs -> Env Term vars -> Name -> Term vars -> Core FC ()
showHole gam env fn (Bind x (Pi c inf ty) sc)
    = do ity <- resugar env (normaliseHoles gam env ty)
         when (showName x) $
           coreLift $ putStrLn $
              showCount c ++ impBracket inf (tidy x ++ " : " ++ show ity)
         showHole gam (Pi c inf ty :: env) fn sc
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

showHole gam env fn ty
    = do coreLift $ putStrLn "-------------------------------------"
         ity <- resugar env (normaliseHoles gam env ty)
         coreLift $ putStrLn $ nameRoot fn ++ " : " ++ show ity

displayType : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              Defs -> (Name, GlobalDef) -> Core FC ()
displayType gam (n, def) 
    = if isHole def
         then showHole gam [] n (type def)
         else do tm <- resugar [] (normaliseHoles gam [] (type def))
                 coreLift $ putStrLn $ show n ++ " : " ++ show tm

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
process (Check (PRef fc fn))
    = do defs <- get Ctxt
         case lookupGlobalName fn (gamma defs) of
              [] => throw (UndefinedName fc fn)
              ts => do traverse (displayType defs) ts
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
    = do tm <- search (MkFC "(interactive)" (0, 0) (0, 0)) 1000 [] n (UN "(interactive)")
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


