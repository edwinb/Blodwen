module TTImp.Reflect

import Core.Context
import Core.Normalise
import public Core.Reflect
import Core.Unify
import Core.TT

import TTImp.TTImp

import Data.List

%default covering

-- TODO: Remaining cases!
export
Reify annot => Reify (RawImp annot) where
  reify defs (NDCon (NS ["Reflect"] (UN "Var")) _ _ [fc, n])
      = do fc' <- reify defs (evalClosure defs fc)
           n' <- reify defs (evalClosure defs n)
           pure (IVar fc' n')
  reify defs (NDCon (NS ["Reflect"] (UN "App")) _ _ [fc, f, a])
      = do fc' <- reify defs (evalClosure defs fc)
           f' <- reify defs (evalClosure defs f)
           a' <- reify defs (evalClosure defs a)
           pure (IApp fc' f' a')
  reify defs _ = Nothing

-- TODO: Remaining cases!
export
Reflect annot => Reflect (RawImp annot) where
  reflect defs env (IVar fc nm)
      = do fc' <- reflect defs env fc
           nm' <- reflect defs env nm
           appCon defs (NS ["Reflect"] (UN "Var")) [fc', nm']
  reflect defs env (IApp fc f a)
      = do fc' <- reflect defs env fc
           f' <- reflect defs env f
           a' <- reflect defs env a
           appCon defs (NS ["Reflect"] (UN "App")) [fc', f', a']
  reflect defs env (IUnquote fc (IVar _ nm))
      = do (count, el) <- defined nm env
           pure (Local Nothing el)
  reflect defs env _ = Nothing

export
Reify FnOpt where
  reify defs (NDCon (NS ["Reflect"] (UN "Inline")) _ _ [])
      = pure Inline
  reify defs (NDCon (NS ["Reflect"] (UN "Hint")) _ _ [t])
      = do t' <- reify defs (evalClosure defs t)
           pure (Hint t')
  reify defs (NDCon (NS ["Reflect"] (UN "GlobalHint")) _ _ [t])
      = do t' <- reify defs (evalClosure defs t)
           pure (GlobalHint t')
  reify defs (NDCon (NS ["Reflect"] (UN "ExternFn")) _ _ [])
      = pure ExternFn
  reify defs (NDCon (NS ["Reflect"] (UN "Invertible")) _ _ [])
      = pure Invertible
  reify defs (NDCon (NS ["Reflect"] (UN "Total")) _ _ [])
      = pure Total
  reify defs (NDCon (NS ["Reflect"] (UN "Covering")) _ _ [])
      = pure Covering
  reify defs (NDCon (NS ["Reflect"] (UN "PartialOK")) _ _ [])
      = pure PartialOK
  reify defs _ = Nothing

export
Reflect FnOpt where
  reflect defs env Inline = getCon defs (NS ["Reflect"] (UN "Inline"))
  reflect defs env (Hint t) 
      = do t' <- reflect defs env t
           appCon defs (NS ["Reflect"] (UN "Hint")) [t']
  reflect defs env (GlobalHint t) 
      = do t' <- reflect defs env t
           appCon defs (NS ["Reflect"] (UN "GlobalHint")) [t']
  reflect defs env ExternFn = getCon defs (NS ["Reflect"] (UN "ExternFn"))
  reflect defs env Invertible = getCon defs (NS ["Reflect"] (UN "Invertible"))
  reflect defs env Total = getCon defs (NS ["Reflect"] (UN "Total"))
  reflect defs env Covering = getCon defs (NS ["Reflect"] (UN "Covering"))
  reflect defs env PartialOK = getCon defs (NS ["Reflect"] (UN "PartialOK"))

export
Reify annot => Reify (ImpTy annot) where
  reify defs (NDCon (NS ["Reflect"] (UN "MkTy")) _ _ [fc, n, ty])
      = do fc' <- reify defs (evalClosure defs fc)
           n' <- reify defs (evalClosure defs n)
           ty' <- reify defs (evalClosure defs ty)
           pure (MkImpTy fc' n' ty')
  reify defs _ = Nothing

export
Reflect annot => Reflect (ImpTy annot) where
  reflect defs env (MkImpTy fc n ty)
      = do fc' <- reflect defs env fc
           n' <- reflect defs env n
           ty' <- reflect defs env ty
           appCon defs (NS ["Reflect"] (UN "MkTy")) [fc', n', ty']

export
Reify annot => Reify (ImpClause annot) where
  reify defs (NDCon (NS ["Reflect"] (UN "PatClause")) _ _ [fc, lhs, rhs])
      = do fc' <- reify defs (evalClosure defs fc)
           lhs' <- reify defs (evalClosure defs lhs)
           rhs' <- reify defs (evalClosure defs rhs)
           pure (PatClause fc' lhs' rhs')
  reify defs (NDCon (NS ["Reflect"] (UN "WithClause")) _ _ [fc, lhs, wval, cs])
      = do fc' <- reify defs (evalClosure defs fc)
           lhs' <- reify defs (evalClosure defs lhs)
           wval' <- reify defs (evalClosure defs wval)
           cs' <- reify defs (evalClosure defs cs)
           pure (WithClause fc' lhs' wval' cs')
  reify defs (NDCon (NS ["Reflect"] (UN "Impossible")) _ _ [fc, lhs])
      = do fc' <- reify defs (evalClosure defs fc)
           lhs' <- reify defs (evalClosure defs lhs)
           pure (ImpossibleClause fc' lhs')
  reify defs _ = Nothing

export
Reflect annot => Reflect (ImpClause annot) where
  reflect defs env (PatClause fc lhs rhs)
      = do fc' <- reflect defs env fc
           lhs' <- reflect defs env lhs
           rhs' <- reflect defs env rhs
           appCon defs (NS ["Reflect"] (UN "PatClause")) [fc', lhs', rhs']
  reflect defs env (WithClause fc lhs wval cs)
      = do fc' <- reflect defs env fc
           lhs' <- reflect defs env lhs
           wval' <- reflect defs env wval
           cs' <- reflect defs env cs
           appCon defs (NS ["Reflect"] (UN "WithClause")) [fc', lhs', wval', cs']
  reflect defs env (ImpossibleClause fc lhs)
      = do fc' <- reflect defs env fc
           lhs' <- reflect defs env lhs
           appCon defs (NS ["Reflect"] (UN "Impossible")) [fc', lhs']

export
Reify DataOpt where
  reify defs (NDCon (NS ["Reflect"] (UN "SearchBy")) _ _ [xs])
      = do xs' <- reify defs (evalClosure defs xs)
           pure (SearchBy xs')
  reify defs (NDCon (NS ["Reflect"] (UN "NoHints")) _ _ [])
      = pure NoHints
  reify defs _ = Nothing

export
Reflect DataOpt where
  reflect defs env (SearchBy xs) 
      = do xs' <- reflect defs env xs
           appCon defs (NS ["Reflect"] (UN "SearchBy")) [xs']
  reflect defs env NoHints = getCon defs (NS ["Reflect"] (UN "Hint"))

export
Reify annot => Reify (ImpData annot) where
  reify defs (NDCon (NS ["Reflect"] (UN "MkData")) _ _ [fc, tyn, ty, opts, cons])
      = do fc' <- reify defs (evalClosure defs fc)
           tyn' <- reify defs (evalClosure defs tyn)
           ty' <- reify defs (evalClosure defs ty)
           opts' <- reify defs (evalClosure defs opts)
           cons' <- reify defs (evalClosure defs cons)
           pure (MkImpData fc' tyn' ty' opts' cons')
  reify defs (NDCon (NS ["Reflect"] (UN "MkLater")) _ _ [fc, tyn, ty])
      = do fc' <- reify defs (evalClosure defs fc)
           tyn' <- reify defs (evalClosure defs tyn)
           ty' <- reify defs (evalClosure defs ty)
           pure (MkImpLater fc' tyn' ty')
  reify defs _ = Nothing

export
Reflect annot => Reflect (ImpData annot) where
  reflect defs env (MkImpData fc n tycon opts cons)
      = do fc' <- reflect defs env fc
           n' <- reflect defs env n
           tycon' <- reflect defs env tycon
           opts' <- reflect defs env opts
           cons' <- reflect defs env cons
           appCon defs (NS ["Reflect"] (UN "MkData")) [fc', n', tycon', opts', cons']
  reflect defs env (MkImpLater fc n tycon)
      = do fc' <- reflect defs env fc
           n' <- reflect defs env n
           tycon' <- reflect defs env tycon
           appCon defs (NS ["Reflect"] (UN "MkLater")) [fc', n', tycon']

export
Reify annot => Reify (ImpDecl annot) where
  reify defs (NDCon (NS ["Reflect"] (UN "Claim")) _ _ [fc, vis, opts, ty])
      = do fc' <- reify defs (evalClosure defs fc)
           vis' <- reify defs (evalClosure defs vis)
           opts' <- reify defs (evalClosure defs opts)
           ty' <- reify defs (evalClosure defs ty)
           pure (IClaim fc' RigW vis' opts' ty')
  reify defs (NDCon (NS ["Reflect"] (UN "Def")) _ _ [fc, n, cs])
      = do fc' <- reify defs (evalClosure defs fc)
           n' <- reify defs (evalClosure defs n)
           cs' <- reify defs (evalClosure defs cs)
           pure (IDef fc' n' cs')
  reify defs (NDCon (NS ["Reflect"] (UN "Data")) _ _ [fc, vis, ddecl])
      = do fc' <- reify defs (evalClosure defs fc)
           vis' <- reify defs (evalClosure defs vis)
           ddecl' <- reify defs (evalClosure defs ddecl)
           pure (IData fc' vis' ddecl')
  reify defs _ = Nothing

export
Reflect annot => Reflect (ImpDecl annot) where
  reflect defs env (IClaim fc _ vis opts ty)
      = do fc' <- reflect defs env fc
           vis' <- reflect defs env vis
           opts' <- reflect defs env opts
           ty' <- reflect defs env ty
           appCon defs (NS ["Reflect"] (UN "Claim")) [fc', vis', opts', ty']
  reflect defs env (IDef fc n cs)
      = do fc' <- reflect defs env fc
           n' <- reflect defs env n
           cs' <- reflect defs env cs
           appCon defs (NS ["Reflect"] (UN "Def")) [fc', n', cs']
  reflect defs env (IData fc vis ddecl)
      = do fc' <- reflect defs env fc
           vis' <- reflect defs env vis
           ddecl' <- reflect defs env ddecl
           appCon defs (NS ["Reflect"] (UN "Data")) [fc', vis', ddecl']
  reflect defs env _ = Nothing

