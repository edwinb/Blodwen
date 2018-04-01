module TTImp.Reflect

import Core.Context
import Core.Normalise
import public Core.Reflect
import Core.Unify
import Core.TT

import TTImp.Elab
import TTImp.ProcessDef
import TTImp.ProcessType
import TTImp.TTImp

%default covering

export
Reflect annot => Reflect (RawImp annot) where
  reflect defs (NDCon (NS ["Reflect"] (UN "Var")) _ _ [fc, n])
      = do fc' <- reflect defs (evalClosure defs fc)
           n' <- reflect defs (evalClosure defs n)
           pure (IVar fc' n')
  reflect defs (NDCon (NS ["Reflect"] (UN "App")) _ _ [fc, f, a])
      = do fc' <- reflect defs (evalClosure defs fc)
           f' <- reflect defs (evalClosure defs f)
           a' <- reflect defs (evalClosure defs a)
           pure (IApp fc' f' a')
  reflect defs _ = Nothing

export
Reify annot => Reify (RawImp annot) where
  reify defs _ = Nothing

export
Reflect FnOpt where
  reflect defs (NDCon (NS ["Reflect"] (UN "Inline")) _ _ [])
      = pure Inline
  reflect defs (NDCon (NS ["Reflect"] (UN "Hint")) _ _ [])
      = pure Hint
  reflect defs (NDCon (NS ["Reflect"] (UN "GlobalHint")) _ _ [])
      = pure GlobalHint
  reflect defs _ = Nothing

export
Reify FnOpt where
  reify defs Inline = getCon defs (NS ["Reflect"] (UN "Inline"))
  reify defs Hint = getCon defs (NS ["Reflect"] (UN "Hint"))
  reify defs GlobalHint = getCon defs (NS ["Reflect"] (UN "GlobalHint"))

export
Reflect annot => Reflect (ImpTy annot) where
  reflect defs (NDCon (NS ["Reflect"] (UN "MkTy")) _ _ [fc, n, ty])
      = do fc' <- reflect defs (evalClosure defs fc)
           n' <- reflect defs (evalClosure defs n)
           ty' <- reflect defs (evalClosure defs ty)
           pure (MkImpTy fc' n' ty')
  reflect defs _ = Nothing

export
Reify annot => Reify (ImpTy annot) where
  reify defs (MkImpTy fc n ty)
      = do fc' <- reify defs fc
           n' <- reify defs n
           ty' <- reify defs ty
           appCon defs (NS ["Reflect"] (UN "MkTy")) [fc', n', ty']

export
Reflect annot => Reflect (ImpClause annot) where
  reflect defs (NDCon (NS ["Reflect"] (UN "PatClause")) _ _ [fc, lhs, rhs])
      = do fc' <- reflect defs (evalClosure defs fc)
           lhs' <- reflect defs (evalClosure defs lhs)
           rhs' <- reflect defs (evalClosure defs rhs)
           pure (PatClause fc' lhs' rhs')
  reflect defs (NDCon (NS ["Reflect"] (UN "Impossible")) _ _ [fc, lhs])
      = do fc' <- reflect defs (evalClosure defs fc)
           lhs' <- reflect defs (evalClosure defs lhs)
           pure (ImpossibleClause fc' lhs')
  reflect defs _ = Nothing

export
Reify annot => Reify (ImpClause annot) where
  reify defs (PatClause fc lhs rhs)
      = do fc' <- reify defs fc
           lhs' <- reify defs lhs
           rhs' <- reify defs rhs
           appCon defs (NS ["Reflect"] (UN "PatClause")) [fc', lhs', rhs']
  reify defs (ImpossibleClause fc lhs)
      = do fc' <- reify defs fc
           lhs' <- reify defs lhs
           appCon defs (NS ["Reflect"] (UN "Impossible")) [fc', lhs']

export
Reflect DataOpt where
  reflect defs (NDCon (NS ["Reflect"] (UN "SearchBy")) _ _ [xs])
      = do xs' <- reflect defs (evalClosure defs xs)
           pure (SearchBy xs')
  reflect defs (NDCon (NS ["Reflect"] (UN "NoHints")) _ _ [])
      = pure NoHints
  reflect defs _ = Nothing

export
Reify DataOpt where
  reify defs (SearchBy xs) 
      = do xs' <- reify defs xs
           appCon defs (NS ["Reflect"] (UN "SearchBy")) [xs']
  reify defs NoHints = getCon defs (NS ["Reflect"] (UN "Hint"))

export
Reflect annot => Reflect (ImpData annot) where
  reflect defs (NDCon (NS ["Reflect"] (UN "MkData")) _ _ [fc, tyn, ty, opts, cons])
      = do fc' <- reflect defs (evalClosure defs fc)
           tyn' <- reflect defs (evalClosure defs tyn)
           ty' <- reflect defs (evalClosure defs opts)
           opts' <- reflect defs (evalClosure defs opts)
           cons' <- reflect defs (evalClosure defs cons)
           pure (MkImpData fc' tyn' ty' opts' cons')
  reflect defs _ = Nothing

export
Reify annot => Reify (ImpData annot) where
  reify defs (MkImpData fc n tycon opts cons)
      = do fc' <- reify defs fc
           n' <- reify defs n
           tycon' <- reify defs tycon
           opts' <- reify defs opts
           cons' <- reify defs cons
           appCon defs (NS ["Reflect"] (UN "MkData")) [fc', n', tycon', opts', cons']

export
Reflect annot => Reflect (ImpDecl annot) where
  reflect defs (NDCon (NS ["Reflect"] (UN "Claim")) _ _ [fc, vis, opts, ty])
      = do fc' <- reflect defs (evalClosure defs fc)
           vis' <- reflect defs (evalClosure defs vis)
           opts' <- reflect defs (evalClosure defs opts)
           ty' <- reflect defs (evalClosure defs ty)
           pure (IClaim fc' vis' opts' ty')
  reflect defs (NDCon (NS ["Reflect"] (UN "Def")) _ _ [fc, n, cs])
      = do fc' <- reflect defs (evalClosure defs fc)
           n' <- reflect defs (evalClosure defs n)
           cs' <- reflect defs (evalClosure defs cs)
           pure (IDef fc' n' cs')
  reflect defs (NDCon (NS ["Reflect"] (UN "Data")) _ _ [fc, vis, ddecl])
      = do fc' <- reflect defs (evalClosure defs fc)
           vis' <- reflect defs (evalClosure defs vis)
           ddecl' <- reflect defs (evalClosure defs ddecl)
           pure (IData fc' vis' ddecl')
  reflect defs _ = Nothing

export
Reify annot => Reify (ImpDecl annot) where
  reify defs (IClaim fc vis opts ty)
      = do fc' <- reify defs fc
           vis' <- reify defs vis
           opts' <- reify defs opts
           ty' <- reify defs ty
           appCon defs (NS ["Reflect"] (UN "Claim")) [fc', vis', opts', ty']
  reify defs (IDef fc n cs)
      = do fc' <- reify defs fc
           n' <- reify defs n
           cs' <- reify defs cs
           appCon defs (NS ["Reflect"] (UN "Def")) [fc', n', cs']
  reify defs (IData fc vis ddecl)
      = do fc' <- reify defs fc
           vis' <- reify defs vis
           ddecl' <- reify defs ddecl
           appCon defs (NS ["Reflect"] (UN "Data")) [fc', vis', ddecl']
  reify defs _ = Nothing

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
