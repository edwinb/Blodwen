module TTImp.RunElab

import Core.Context
import Core.Normalise
import public Core.Reflect
import Core.Unify
import Core.TT

import TTImp.Elab
import TTImp.ProcessDef
import TTImp.ProcessType
import TTImp.Reflect
import TTImp.TTImp

elabScript : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Reflect annot =>
             annot -> Elaborator annot ->
             Env Term vars -> NestedNames vars -> NF vars -> 
             Core annot (NF vars) 
elabScript {vars} loc elab env nest tm@(NDCon (NS ["Reflect"] (UN n)) _ _ args)
    = do defs <- get Ctxt
         elabCon defs n args
  where
    failWith : Defs -> Core annot a
    failWith defs = throw (BadRunElab loc (quote (noGam defs) env tm))

    doReflect : Reflect a => NF vars -> Core annot a
    doReflect tm 
        = do defs <- get Ctxt
             case reflect {a} defs tm of
                  Nothing => failWith defs
                  Just x => pure x

    retReify : Reify a => Defs -> a -> Core annot (NF vars)
    retReify defs tm 
        = case reify defs tm of
               Nothing => throw (GenericMsg loc "Unsupported reification")
               Just res => pure (nf defs env (embed res))

    retUnit : Core annot (NF vars)
    retUnit = pure (NDCon (NS ["Stuff"] (UN "MkUnit")) 0 0 [])

    elabCon : Defs -> String -> List (Closure vars) -> Core annot (NF vars)
    elabCon defs "Pure" [_, arg]
        = pure (evalClosure defs arg)
    elabCon defs ">>=" [_, _, act, k]
        = do p <- elabScript loc elab env nest (evalClosure defs act)
             case evalClosure defs k of
                  NBind x (Lam _ _ _) sc =>
                        elabScript loc elab env nest 
                            (sc (toClosure False env (quote defs env p)))
                  tm => failWith defs
    elabCon defs "Log" [i, msg]
        = do i' <- doReflect (evalClosure defs i)
             msg' <- doReflect (evalClosure defs msg)
             log (cast {from = Int} i') msg'
             retUnit
    elabCon defs "GenSym" [root]
        = do root' <- doReflect (evalClosure defs root)
             n <- genName root'
             retReify defs n
    elabCon defs "DeclareType" [fn, fty]
        = do fn <- doReflect (evalClosure defs fn)
             ty <- doReflect (evalClosure defs fty)
             processType elab env nest Public [] (MkImpTy loc fn ty)
             retUnit
    elabCon defs "DefineFunc" [fn, cs]
        = do fn <- doReflect (evalClosure defs fn)
             cs <- doReflect (evalClosure defs cs)
             processDef elab env nest loc fn cs
             retUnit
    elabCon defs n args = failWith defs
elabScript loc elab env nest tm 
    = do defs <- get Ctxt
         throw (BadRunElab loc (quote (noGam defs) env tm))

export
processReflect : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST (UState annot)} ->
                 {auto i : Ref ImpST (ImpState annot)} ->
                 Reflect annot =>
                 annot ->
                 Elaborator annot ->
                 Env Term vars -> NestedNames vars -> RawImp annot -> 
                 Core annot ()
processReflect loc elab env nest tm
    = do (etm, ety) <- inferTerm elab (UN "%runElab") env nest NONE InExpr tm
         defs <- get Ctxt
         res <- elabScript loc elab env nest (nf defs env etm)
         log 0 $ "Elab script ended with " ++ show (quote defs env res)
         pure ()
