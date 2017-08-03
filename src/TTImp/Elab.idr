module TTImp.Elab

import TTImp.TTImp
import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT
import Core.Typecheck
import Core.Unify

import public Control.ST
import public Control.ST.Exception
import public Control.ST.ImplicitCall

import Data.List

%default covering

public export
data InferError : Type -> Type where
     CoreError : annot -> Error -> InferError annot
     Undefined : annot -> Name -> InferError annot
     CantUnify : annot -> Env Term vars -> Term vars -> Term vars ->
                 InferError annot
     GenericError : annot -> String -> InferError annot

export
interface (Exception m (InferError annot), CtxtManage m) =>
          InferCtxt (m : Type -> Type) annot | m where

export
(Exception m (InferError annot), CtxtManage m) => InferCtxt m annot where

parameters (ctxt : Var, ustate : Var)
  convert : CtxtManage m => 
            annot ->
            Env Term vars ->
            Term vars -> Term vars -> 
            ST m (List Name) [ctxt ::: Defs, ustate ::: UState]
  convert loc env x y 
      = catch (do vs <- unify ctxt ustate env x y
                  solveConstraints ctxt ustate
                  pure vs)
              (\_ => throw (CantConvert env x y))

  checkExp : CtxtManage m =>
             annot ->
             Env Term vars ->
             (term : Term vars) -> (got : Term vars) -> 
             (exp : Maybe (Term vars)) ->
             ST m (Term vars, Term vars) [ctxt ::: Defs, ustate ::: UState]
  checkExp loc env tm got Nothing
      = pure (tm, got)
  checkExp loc env tm got (Just exp) 
      = do vars <- convert loc env got exp
           pure (tm, got)

  inventFnType : CtxtManage m =>
                 Env Term vars ->
                 (bname : Name) ->
                 ST m (Term vars, Term (bname :: vars))
                      [ctxt ::: Defs, ustate ::: UState]
  inventFnType env bname
      = do an <- genName ustate "argh"
           scn <- genName ustate "sch"
           let argTy = mkConstantApp an env
           let scTy = mkConstantApp scn (Pi Explicit argTy :: env)
           pure (argTy, scTy)

  mutual
    check : CtxtManage m =>
            Env Term vars ->
            (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
            ST m (Term vars, Term vars) [ctxt ::: Defs, ustate ::: UState]
    check env (IVar loc x) expected 
        = do (x', ty) <- infer ctxt env (RVar x)
             checkExp loc env x' ty expected
    check env (IPi loc plicity n ty retTy) expected 
        = checkPi loc env plicity n ty retTy expected
    check env (ILam loc n ty scope) expected
        = checkLam loc env n ty scope expected
    check env (ILet loc n nTy nVal scope) expected 
        = checkLet loc env n nTy nVal scope expected
    check env (IApp loc fn arg) expected 
        = do (fntm, fnty) <- check env fn Nothing
             gam <- getCtxt ctxt
             case nf gam env fnty of
                  NBind _ (Pi _ ty) scdone =>
                    do (argtm, argty) <- check env arg (Just (quote empty env ty))
                       let sc' = scdone (toClosure env argtm)
                       checkExp loc env (App fntm argtm)
                                    (quote gam env sc') expected
                  _ => 
                    do bn <- genName ustate "aTy"
                       (expty, scty) <- inventFnType env bn
                       (argtm, argty) <- 
                           check env arg (Just (Bind bn (Pi Explicit expty) scty))
                       checkExp loc env (App fntm argtm)
                                    (Bind bn (Let argtm argty) scty) expected
    check env (IPrimVal loc x) expected 
        = do (x', ty) <- infer ctxt env (RPrimVal x)
             checkExp loc env x' ty expected
    check env (IType loc) exp
        = checkExp loc env TType TType exp
    check env (IBindVar loc n) expected
        = ?ibindvar
    check env (Implicit loc) Nothing
        = do t <- addHole ctxt ustate env TType
             let hty = mkConstantApp t env
             n <- addHole ctxt ustate env hty
             pure (mkConstantApp n env, hty)
    check env (Implicit loc) (Just expected) 
        = do n <- addHole ctxt ustate env expected
             pure (mkConstantApp n env, expected)
    
    checkPi : CtxtManage m =>
              annot -> Env Term vars ->
              PiInfo -> Name -> 
              (argty : RawImp annot) -> (retty : RawImp annot) ->
              Maybe (Term vars) ->
              ST m (Term vars, Term vars) [ctxt ::: Defs, ustate ::: UState]
    checkPi loc env info n argty retty expected
        = do (tyv, tyt) <- Elab.check env argty (Just TType)
             let env' : Env Term (n :: _) = Pi info tyv :: env
             (scopev, scopet) <- Elab.check env' retty (Just TType)
             checkExp loc env (Bind n (Pi info tyv) scopev) 
                              TType expected

    checkLam : CtxtManage m =>
               annot -> Env Term vars ->
               Name -> (ty : RawImp annot) -> (scope : RawImp annot) ->
               Maybe (Term vars) ->
               ST m (Term vars, Term vars) [ctxt ::: Defs, ustate ::: UState]
    checkLam loc env n ty scope (Just (Bind bn (Pi Explicit pty) psc))
        = do (tyv, tyt) <- check env ty (Just TType)
             (scopev, scopet) <- check (Pi Explicit pty :: env) scope (Just psc)
             checkExp loc env (Bind bn (Lam tyv) scopev)
                          (Bind bn (Pi Explicit tyv) scopet)
                          (Just (Bind bn (Pi Explicit pty) psc))
    checkLam loc env n ty scope expected
        = do (tyv, tyt) <- check env ty (Just TType)
             let env' : Env Term (n :: _) = Pi Explicit tyv :: env
             (scopev, scopet) <- check env' scope Nothing
             checkExp loc env (Bind n (Lam tyv) scopev)
                          (Bind n (Pi Explicit tyv) scopet)
                          expected
    
    checkLet : CtxtManage m =>
               annot -> Env Term vars ->
               Name -> (val : RawImp annot) -> 
               (ty : RawImp annot) -> (scope : RawImp annot) ->
               Maybe (Term vars) ->
               ST m (Term vars, Term vars) [ctxt ::: Defs, ustate ::: UState]
    checkLet loc env n val ty scope expected
        = do (tyv, tyt) <- check env ty (Just TType)
             (valv, valt) <- check env val (Just tyv)
             let env' : Env Term (n :: _) = Let valv tyv :: env
             (scopev, scopet) <- check env' scope (map weaken expected)
             checkExp loc env (Bind n (Let valv tyv) scopev)
                              (Bind n (Let valv tyv) scopet)
                              expected
 
export
inferTerm : CtxtManage m => 
            (ctxt : Var) -> (ustate : Var) -> (term : RawImp annot) ->
            ST m (Term [], Term []) [ctxt ::: Defs, ustate ::: UState]
inferTerm ctxt ustate tm
    = do (chktm, ty) <- check ctxt ustate [] tm Nothing
         dumpConstraints ctxt ustate
         pure (chktm, ty)
