module TTImp.ProcessDef

import Core.TT
import Core.Unify
import Core.Context
import Core.CaseTree
import Core.Normalise

import TTImp.Elab
import TTImp.TTImp

import Control.Catchable

mutual
  mismatchNF : Gamma -> NF vars -> NF vars -> Bool
  mismatchNF gam (NTCon _ xt _ xargs) (NTCon _ yt _ yargs) 
      = if xt /= yt 
           then True
           else any (mismatch gam) (zip xargs yargs) 
  mismatchNF gam (NDCon _ xt _ xargs) (NDCon _ yt _ yargs) 
      = if xt /= yt
           then True
           else any (mismatch gam) (zip xargs yargs) 
  mismatchNF gam (NPrimVal xc) (NPrimVal yc) = xc /= yc
  mismatchNF _ _ _ = False

  mismatch : Gamma -> (Closure vars, Closure vars) -> Bool
  mismatch gam (x, y) = mismatchNF gam (evalClosure gam x) (evalClosure gam y)

-- If the terms have the same type constructor at the head, and one of
-- the argument positions has different constructors at its head, then this
-- is an impossible case, so return True
impossibleOK : Gamma -> NF vars -> NF vars -> Bool
impossibleOK gam (NTCon xn xt xa xargs) (NTCon tn yt ya yargs)
    = any (mismatch gam) (zip xargs yargs)
impossibleOK _ _ _ = False

checkClause : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              Elaborator annot ->
              Name ->
              Env Term vars -> NestedNames vars -> ImpClause annot ->
              Core annot (Maybe Clause)
checkClause elab defining env nest (ImpossibleClause loc lhs_raw)
    = handle
         (do lhs_raw <- lhsInCurrentNS nest lhs_raw
             (lhs_in, lhsty_in) <- inferTerm elab defining env nest PATTERN InLHS lhs_raw
             gam <- getCtxt
             let lhs = normaliseHoles gam env lhs_in
             let lhsty = normaliseHoles gam env lhsty_in
             throw (ValidCase loc env (Left lhs)))
         (\err => case err of
                       ValidCase _ _ _ => throw err
                       WhenUnifying _ env l r err
                           => do gam <- getCtxt
                                 if impossibleOK gam (nf gam env l) (nf gam env r)
                                    then pure Nothing
                                    else throw (ValidCase loc env (Right err))
                       _ => throw (ValidCase loc env (Right err)))
checkClause elab defining env nest (PatClause loc lhs_raw rhs_raw)
    = do lhs_raw <- lhsInCurrentNS nest lhs_raw
         log 5 ("Checking LHS: " ++ show lhs_raw)
         (lhs_in, lhsty_in) <- inferTerm elab defining env nest PATTERN InLHS lhs_raw
         gam <- getCtxt
         let lhs = normaliseHoles gam env lhs_in
         let lhsty = normaliseHoles gam env lhsty_in
         (vs ** (env', nest', lhspat, reqty)) <- extend env nest lhs lhsty
         log 3 ("LHS: " ++ show lhs ++ " : " ++ show reqty)
         rhs <- checkTerm elab defining env' nest' NONE InExpr rhs_raw reqty
         log 3 ("Clause: " ++ show lhs ++ " = " ++ show rhs)
         pure (Just (MkClause env' lhspat rhs))
  where
    extend : Env Term vars -> NestedNames vars -> 
             Term vars -> Term vars ->
             Core annot (vars' ** (Env Term vars', NestedNames vars', 
                                   Term vars', Term vars'))
    extend env nest (Bind n (PVar tmsc) sc) (Bind n' (PVTy _) tysc) with (nameEq n n')
      extend env nest (Bind n (PVar tmsc) sc) (Bind n' (PVTy _) tysc) | Nothing 
            = throw (InternalError "Names don't match in pattern type")
      extend env nest (Bind n (PVar tmsc) sc) (Bind n (PVTy _) tysc) | (Just Refl) 
            = extend (PVar tmsc :: env) (weaken nest) sc tysc
    extend env nest (Bind n (PLet tmv tmt) sc) (Bind n' (PLet _ _) tysc) with (nameEq n n')
      extend env nest (Bind n (PLet tmv tmt) sc) (Bind n' (PLet _ _) tysc) | Nothing 
            = throw (InternalError "Names don't match in pattern type")
      extend env nest (Bind n (PLet tmv tmt) sc) (Bind n (PLet _ _) tysc) | (Just Refl) 
            = extend (PLet tmv tmt :: env) (weaken nest) sc tysc
    extend env nest tm ty = pure (_ ** (env, nest, tm, ty))

export
processDef : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             Env Term vars -> NestedNames vars -> annot ->
             Name -> List (ImpClause annot) -> 
             Core annot ()
processDef elab env nest loc n_in cs_raw
    = do gam <- getCtxt
         n <- inCurrentNS n_in
         case lookupDefTyExact n gam of
              Nothing => throw (NoDeclaration loc n)
              Just (None, ty) =>
                do cs <- traverse (checkClause elab n env nest) cs_raw
                   addFnDef loc Public (MkFn n ty (mapMaybe id cs))
                   gam <- getCtxt
                   log 3 $
                      case lookupDefExact n gam of
                           Just (PMDef _ args t) =>
                              "Case tree for " ++ show n ++ "\n\t" ++
                              show args ++ " " ++ show t
                           _ => "No case tree for " ++ show n
              Just (_, ty) => throw (AlreadyDefined loc n)
