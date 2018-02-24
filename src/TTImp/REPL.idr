module TTImp.REPL

import Core.AutoSearch
import Core.Context
import Core.Normalise
import Core.TT
import Core.Unify

import TTImp.Elab
import TTImp.ProcessTTImp
import TTImp.TTImp

import Parser.REPL

import Control.Catchable

%default covering

showInfo : (Name, Def) -> Core annot ()
showInfo (n, d) = coreLift $ putStrLn (show n ++ " ==> " ++ show d)

-- Returns 'True' if the REPL should continue
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState ())} ->
          ImpREPL () -> Core () Bool
process (Eval ttimp)
    = do i <- newRef ImpST (initImpState {annot = ()})
         (tm, ty) <- inferTerm elabTop (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         gam <- get Ctxt
         coreLift (putStrLn (show (normalise gam [] tm) ++ " : " ++
                             show (normalise gam [] ty)))
         pure True
process (Check ttimp)
    = do i <- newRef ImpST (initImpState {annot = ()})
         (tm, ty) <- inferTerm elabTop (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         gam <- get Ctxt
         coreLift (putStrLn (show tm ++ " : " ++
                             show (normaliseHoles gam [] ty)))
         pure True
process (ProofSearch n)
    = do tm <- search () 1000 n
         gam <- get Ctxt
         coreLift (putStrLn (show (normalise gam [] tm)))
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
               {auto u : Ref UST (UState ())} ->
               ImpREPL () -> Core () Bool
processCatch cmd
    = catch (process cmd) (\err => do coreLift (putStrLn (show err))
                                      pure True)

export
repl : {auto c : Ref Ctxt Defs} ->
       {auto u : Ref UST (UState ())} ->
       Core () ()
repl
    = do coreLift (putStr "Blodwen> ")
         inp <- coreLift getLine
         case runParser inp command of
              Left err => do coreLift (printLn err)
                             repl
              Right cmd =>
                  do if !(processCatch cmd)
                        then repl
                        else pure ()

