module TTImp.ProcessDef

import Core.TT
import Core.Unify
import Core.Context
import Core.CaseTree
import Core.Normalise

import TTImp.Elab
import TTImp.TTImp

import Control.Catchable

checkClause : {auto c : Ref Ctxt Defs} ->
              {auto e : Ref UST (UState annot)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              Elaborator annot ->
              Name ->
              Env Term vars -> NestedNames vars -> ImpClause annot ->
              Core annot Clause
checkClause elab defining env nest (MkImpClause loc lhs_raw rhs_raw)
    = do lhs_raw <- lhsInCurrentNS nest lhs_raw
         (lhs_in, lhsty_in) <- inferTerm elab defining env nest PATTERN InLHS lhs_raw
         gam <- getCtxt
         let lhs = normaliseHoles gam env lhs_in
         let lhsty = normaliseHoles gam env lhsty_in
         (vs ** (env', nest', lhspat, reqty)) <- extend env nest lhs lhsty
         log 3 ("LHS: " ++ show lhs ++ " : " ++ show reqty)
         rhs <- checkTerm elab defining env' nest' NONE InExpr rhs_raw reqty
         log 3 ("Clause: " ++ show lhs ++ " = " ++ show rhs)
         pure (MkClause env' lhspat rhs)
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
                do cs <- traverse (\x => checkClause elab n env nest x) cs_raw
                   addFnDef loc Public (MkFn n ty cs)
                   gam <- getCtxt
                   log 3 $
                      case lookupDefExact n gam of
                           Just (PMDef _ args t) =>
                              "Case tree for " ++ show n ++ "\n\t" ++
                              show args ++ " " ++ show t
                           _ => "No case tree for " ++ show n
              Just (_, ty) => throw (AlreadyDefined loc n)
