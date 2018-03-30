module TTImp.Reflect

import Core.Context
import Core.Normalise
import Core.TT
import Core.Unify

import TTImp.Elab
import TTImp.ProcessDef
import TTImp.ProcessType
import TTImp.TTImp

%default covering

interface Reflect annot a where
  reflect : annot -> Defs -> NF vars -> Maybe a

Reflect annot String where
  reflect loc defs (NPrimVal (Str str)) = pure str
  reflect loc defs _ = Nothing

Reflect annot Name where
  reflect loc defs (NDCon (NS ["Reflect"] (UN "UN")) _ _ [str])
      = do str' <- reflect loc defs (evalClosure defs str)
           pure (UN str')
  reflect loc defs _ = Nothing

Reflect annot (RawImp annot) where
  reflect loc defs (NDCon (NS ["Reflect"] (UN "Var")) _ _ [n])
      = do n' <- reflect loc defs (evalClosure defs n)
           pure (IVar loc n')
  reflect loc defs (NDCon (NS ["Reflect"] (UN "App")) _ _ [f, a])
      = do f' <- reflect loc defs (evalClosure defs f)
           a' <- reflect loc defs (evalClosure defs a)
           pure (IApp loc f' a')
  reflect loc defs _ = Nothing

Reflect annot (ImpClause annot) where
  reflect loc defs (NDCon (NS ["Reflect"] (UN "PatClause")) _ _ [lhs, rhs])
      = do lhs' <- reflect loc defs (evalClosure defs lhs)
           rhs' <- reflect loc defs (evalClosure defs rhs)
           pure (PatClause loc lhs' rhs')
  reflect loc defs (NDCon (NS ["Reflect"] (UN "Impossible")) _ _ [lhs])
      = do lhs' <- reflect loc defs (evalClosure defs lhs)
           pure (ImpossibleClause loc lhs')
  reflect loc defs _ = Nothing

Reflect annot a => Reflect annot (List a) where
  reflect loc defs (NDCon (NS _ (UN "Nil")) _ _ _)
      = pure []
  reflect loc defs (NDCon (NS _ (UN "::")) _ _ [_, x, xs])
      = do x' <- reflect loc defs (evalClosure defs x)
           xs' <- reflect loc defs (evalClosure defs xs)
           pure (x' :: xs')
  reflect loc defs _ = Nothing

elabScript : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             annot -> Elaborator annot ->
             Env Term vars -> NestedNames vars -> NF vars -> 
             Core annot (NF vars) 
elabScript {vars} loc elab env nest tm@(NDCon (NS ["Reflect"] (UN n)) _ _ args)
    = do defs <- get Ctxt
         elabCon defs n args
  where
    failWith : Defs -> Core annot a
    failWith defs = throw (BadRunElab loc (quote (noGam defs) env tm))

    doReflect : Reflect annot a => NF vars -> Core annot a
    doReflect tm = 
        do defs <- get Ctxt
           case reflect {a} loc defs tm of
                Nothing => failWith defs
                Just x => pure x

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
        = do let NPrimVal (I i') = evalClosure defs i
                  | _ => failWith defs
             let NPrimVal (Str msg') = evalClosure defs msg
                  | _ => failWith defs
             log (cast i') msg'
             retUnit
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
