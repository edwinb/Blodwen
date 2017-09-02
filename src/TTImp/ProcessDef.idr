module TTImp.ProcessDef

import Core.TT
import Core.Unify
import Core.Context
import Core.Normalise

import TTImp.Elab
import TTImp.TTImp

import Control.Catchable
import Control.Monad.StateE

checkClause : Env Term vars -> ImpClause annot ->
              Core annot [Ctxt ::: Defs, UST ::: UState annot] Clause
checkClause env (MkImpClause loc lhs_raw rhs_raw)
    = do -- putStrLn $ "CHECKING " ++ show lhs_raw ++ " = " ++ show rhs_raw
         (lhs_in, lhsty_in) <- inferTerm env PATTERN InLHS lhs_raw
         gam <- getCtxt
         let lhs = normaliseHoles gam env lhs_in
         let lhsty = normaliseHoles gam env lhsty_in
         (vs ** (env', lhspat, reqty)) <- extend env lhs lhsty
         log 5 (show lhs ++ " : " ++ show reqty)
         rhs <- checkTerm env' NONE InExpr rhs_raw reqty
         log 2 (show lhs ++ " = " ++ show rhs)
         pure (MkClause env' lhspat rhs)
  where
    extend : Env Term vars -> Term vars -> Term vars ->
             Core annot [Ctxt ::: Defs, UST ::: UState annot] 
                  (vars' ** (Env Term vars', Term vars', Term vars'))
    extend env (Bind n (PVar tmsc) sc) (Bind n' (PVTy _) tysc) with (nameEq n n')
      extend env (Bind n (PVar tmsc) sc) (Bind n' (PVTy _) tysc) | Nothing 
            = throw (InternalError "Names don't match in pattern type")
      extend env (Bind n (PVar tmsc) sc) (Bind n (PVTy _) tysc) | (Just Refl) 
            = extend (PVar tmsc :: env) sc tysc
    extend env tm ty = pure (_ ** (env, tm, ty))

export
processDef : Env Term vars -> annot ->
             Name -> List (ImpClause annot) -> 
             Core annot [Ctxt ::: Defs, UST ::: UState annot,
                         ImpST ::: ImpState annot] ()
processDef env loc n cs_raw
    = do gam <- getCtxt
         case lookupDefTy n gam of
              Nothing => throw (NoDeclaration loc n)
              Just (None, ty) =>
                do cs <- traverse (\x => checkClause env x) cs_raw
                   addFnDef loc Public (MkFn n ty cs)
              Just (_, ty) => throw (AlreadyDefined loc n)
