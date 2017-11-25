module TTImp.REPL

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

-- Returns 'True' if the REPL should continue
process : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState ())} ->
          ImpREPL () -> Core () Bool
process (Eval ttimp)
    = do i <- newRef ImpST (initImpState {annot = ()})
         (tm, ty) <- inferTerm elabTop (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         gam <- getCtxt
         coreLift (putStrLn (show (normalise gam [] tm) ++ " : " ++
                             show (normalise gam [] ty)))
         pure True
process (Check ttimp)
    = do i <- newRef ImpST (initImpState {annot = ()})
         (tm, ty) <- inferTerm elabTop (UN "[input]") 
                               [] (MkNested []) NONE InExpr ttimp 
         gam <- getCtxt
         coreLift (putStrLn (show tm ++ " : " ++
                             show (normalise gam [] ty)))
         pure True
process (ProofSearch n)
    = throw (InternalError "Proof search not yet implemented")
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

