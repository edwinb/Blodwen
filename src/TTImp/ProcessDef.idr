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
              Elaborator annot ->
              Env Term vars -> ImpClause annot ->
              Core annot Clause
checkClause elab env (MkImpClause loc lhs_raw rhs_raw)
    = do -- putStrLn $ "CHECKING " ++ show lhs_raw ++ " = " ++ show rhs_raw
         (lhs_in, lhsty_in) <- inferTerm elab env PATTERN InLHS lhs_raw
         gam <- getCtxt
         let lhs = normaliseHoles gam env lhs_in
         let lhsty = normaliseHoles gam env lhsty_in
         (vs ** (env', lhspat, reqty)) <- extend env lhs lhsty
         log 5 (show lhs ++ " : " ++ show reqty)
         rhs <- checkTerm elab env' NONE InExpr rhs_raw reqty
         log 3 (show lhs ++ " = " ++ show rhs)
         pure (MkClause env' lhspat rhs)
  where
    extend : Env Term vars -> Term vars -> Term vars ->
             Core annot (vars' ** (Env Term vars', Term vars', Term vars'))
    extend env (Bind n (PVar tmsc) sc) (Bind n' (PVTy _) tysc) with (nameEq n n')
      extend env (Bind n (PVar tmsc) sc) (Bind n' (PVTy _) tysc) | Nothing 
            = throw (InternalError "Names don't match in pattern type")
      extend env (Bind n (PVar tmsc) sc) (Bind n (PVTy _) tysc) | (Just Refl) 
            = extend (PVar tmsc :: env) sc tysc
    extend env tm ty = pure (_ ** (env, tm, ty))

export
processDef : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             Env Term vars -> annot ->
             Name -> List (ImpClause annot) -> 
             Core annot ()
processDef elab env loc n cs_raw
    = do gam <- getCtxt
         case lookupDefTy n gam of
              Nothing => throw (NoDeclaration loc n)
              Just (None, ty) =>
                do cs <- traverse (\x => checkClause elab env x) cs_raw
                   addFnDef loc Public (MkFn n ty cs)
                   gam <- getCtxt
                   log 3 $
                      case lookupDef n gam of
                           Just (PMDef _ args t) =>
                              "Case tree for " ++ show n ++ "\n\t" ++
                              show args ++ " " ++ show t
                           _ => "No case tree for " ++ show n
              Just (_, ty) => throw (AlreadyDefined loc n)
