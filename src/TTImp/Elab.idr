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

-- How the elaborator should deal with IBindVar:
-- * NONE: IBindVar is not valid (rhs of an definition, top level expression)
-- * PI: Bind implicits as Pi, in the appropriate scope
-- * PATT: Bind implicits as PVar, but only at the top level
public export
data ImplicitMode = NONE | PI | PATTERN

export
interface (Exception m (InferError annot), CtxtManage m) =>
          InferCtxt (m : Type -> Type) annot | m where

export
(Exception m (InferError annot), CtxtManage m) => InferCtxt m annot where

record ElabState (vars : List Name) where
  constructor MkElabState
  boundNames : List (Name, (Term vars, Term vars))
                  -- implicit pattern/type variable bindings and the 
                  -- term/type they elaborated to
  toBind : List (Name, (Term vars, Term vars))
                  -- implicit pattern/type variables which haven't been
                  -- bound yet

initEState : ElabState vars
initEState = MkElabState [] []

EState : List Name -> Type
EState vs = State (ElabState vs)

weakenEState : (estate : Var) ->
               ST m () [estate ::: EState vs :-> EState (n :: vs)]
weakenEState estate
    = do est <- read estate
         write estate (MkElabState (map wknTms (boundNames est))
                                   (map wknTms (toBind est)))
  where
    wknTms : (Name, (Term vs, Term vs)) -> 
             (Name, (Term (n :: vs), Term (n :: vs)))
    wknTms (f, (x, y)) = (f, (weaken x, weaken y))

clearEState : (estate : Var) ->
              ST m () [estate ::: EState (n :: vs) :-> EState vs]
clearEState estate = write estate initEState

clearToBind : (estate : Var) ->
              ST m () [estate ::: EState vs :-> EState vs]
clearToBind estate = 
    do est <- read estate
       write estate (record { toBind = [] } est)
    
bindImplicits : Int -> 
                List (Name, (Term vars, Term vars)) ->
                Term vars -> Term vars
bindImplicits i [] scope = scope
bindImplicits i ((n, (tm, ty)) :: imps) scope
    = let scope' = bindImplicits (i + 1) imps scope
          tmpN = MN "unb" i
          repName = repName (Ref Bound tmpN) scope' in
          Bind n (Pi Implicit ty) (refToLocal tmpN n repName)
  where
    -- Replace the name applied to *any* arguments with another term
    repName : (new : Term vars) -> Term vars -> Term vars
    repName new (Local p) = Local p
    repName new (Ref nt fn)
        = case nameEq n fn of
               Nothing => Ref nt fn
               Just Refl => new
    repName new (Bind y b tm) 
        = Bind y (assert_total (map (repName new) b)) 
                 (repName (weaken new) tm)
    repName new (App fn arg) 
        = case getFn fn of
               Ref nt fn' =>
                   case nameEq n fn' of
                        Nothing => App (repName new fn) (repName new arg)
                        Just Refl => new
               _ => App (repName new fn) (repName new arg)
    repName new (PrimVal y) = PrimVal y
    repName new Erased = Erased
    repName new TType = TType


parameters (ctxt : Var, ustate : Var, estate : Var)
  convert : CtxtManage m => 
            annot ->
            Env Term vars ->
            Term vars -> Term vars -> 
            ST m (List Name) [ctxt ::: Defs, ustate ::: UState,
                              estate ::: EState vars]
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
             ST m (Term vars, Term vars) 
                  [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
  checkExp loc env tm got Nothing
      = pure (tm, got)
  checkExp loc env tm got (Just exp) 
      = do constr <- convert loc env got exp
           case constr of
                [] => pure (tm, got)
                cs => do gam <- getCtxt ctxt
                         c <- addConstant ctxt ustate env tm exp cs
                         pure (mkConstantApp c env, got)

  inventFnType : CtxtManage m =>
                 Env Term vars ->
                 (bname : Name) ->
                 ST m (Term vars, Term (bname :: vars))
                      [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
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
            ST m (Term vars, Term vars) 
                 [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
    check env tm exp = checkImp env (insertImpLam env tm exp) exp

    insertImpLam : Env Term vars ->
                   (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
                   RawImp annot
    insertImpLam env tm Nothing = tm
    insertImpLam env tm (Just ty) = tm -- TODO

    checkImp : CtxtManage m =>
               Env Term vars ->
               (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
               ST m (Term vars, Term vars) 
                    [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
    checkImp env (IVar loc x) expected 
        = do (x', varty) <- infer ctxt env (RVar x)
             gam <- getCtxt ctxt
             -- If the variable has an implicit binder in its type, add
             -- the implicits here
             (ty, imps) <- getImps loc env (nf gam env varty) []
             checkExp loc env (apply x' imps) (quote empty env ty) expected
    checkImp env (IPi loc plicity n ty retTy) expected 
        = checkPi loc env plicity n ty retTy expected
    checkImp env (ILam loc n ty scope) expected
        = checkLam loc env n ty scope expected
    checkImp env (ILet loc n nTy nVal scope) expected 
        = checkLet loc env n nTy nVal scope expected
    checkImp env (IApp loc fn arg) expected 
        = do (fntm, fnty) <- check env fn Nothing
             gam <- getCtxt ctxt
             -- If the function has an implicit binder in its type, add
             -- the implicits here
             (scopeTy, impArgs) <- getImps loc env (nf gam env fnty) []
             case scopeTy of
                  NBind _ (Pi _ ty) scdone =>
                    do (argtm, argty) <- check env arg (Just (quote empty env ty))
                       let sc' = scdone (toClosure env argtm)
                       checkExp loc env (App (apply fntm impArgs) argtm)
                                    (quote gam env sc') expected
                  _ => 
                    do bn <- genName ustate "aTy"
                       (expty, scty) <- inventFnType env bn
                       (argtm, argty) <- 
                           check env arg (Just (Bind bn (Pi Explicit expty) scty))
                       checkExp loc env (App fntm argtm)
                                    (Bind bn (Let argtm argty) scty) expected
    checkImp env (IPrimVal loc x) expected 
        = do (x', ty) <- infer ctxt env (RPrimVal x)
             checkExp loc env x' ty expected
    checkImp env (IType loc) exp
        = checkExp loc env TType TType exp
    checkImp env (IBindVar loc n) Nothing
        = do t <- addHole ctxt ustate env TType
             let hty = mkConstantApp t env
             est <- read estate
             case lookup n (boundNames est) of
                  Nothing =>
                    do tm <- addBoundName ctxt ustate n env hty
                       write estate 
                           (record { boundNames $= ((n, (tm, hty)) ::),
                                     toBind $= ((n, (tm, hty)) ::) } est)
                       pure (tm, hty)
                  Just (tm, ty) =>
                       pure (tm, ty)
    checkImp env (IBindVar loc n) (Just expected) 
        = do est <- read estate
             case lookup n (boundNames est) of
                  Nothing =>
                    do tm <- addBoundName ctxt ustate n env expected
                       write estate 
                           (record { boundNames $= ((n, (tm, expected)) ::),
                                     toBind $= ((n, (tm, expected)) :: ) } est)
                       pure (tm, expected)
                  Just (tm, ty) =>
                       checkExp loc env tm ty (Just expected)
    checkImp env (Implicit loc) Nothing
        = do t <- addHole ctxt ustate env TType
             let hty = mkConstantApp t env
             n <- addHole ctxt ustate env hty
             pure (mkConstantApp n env, hty)
    checkImp env (Implicit loc) (Just expected) 
        = do n <- addHole ctxt ustate env expected
             pure (mkConstantApp n env, expected)
   
    -- Get the implicit arguments that need to be inserted at this point
    -- in a function application. Do this by reading off implicit Pis
    -- in the expected type ('ty') and adding new holes for each.
    -- Return the (normalised) remainder of the type, and the list of
    -- implicits added
    getImps : CtxtManage m =>
              annot -> Env Term vars ->
              (ty : NF vars) -> List (Term vars) ->
              ST m (NF vars, List (Term vars)) 
                   [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
    getImps loc env (NBind _ (Pi Implicit ty) sc) imps
        = do n <- addHole ctxt ustate env (quote empty env ty)
             let arg = mkConstantApp n env
             getImps loc env (sc (toClosure env arg)) (arg :: imps)
    getImps loc env ty imps = pure (ty, reverse imps)

    checkPi : CtxtManage m =>
              annot -> Env Term vars ->
              PiInfo -> Name -> 
              (argty : RawImp annot) -> (retty : RawImp annot) ->
              Maybe (Term vars) ->
              ST m (Term vars, Term vars) 
                   [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
    checkPi loc env info n argty retty expected
        = do (tyv, tyt) <- Elab.check env argty (Just TType)
             let env' : Env Term (n :: _) = Pi info tyv :: env
             est <- read estate
             let argImps = reverse $ toBind est
             clearToBind estate
             weakenEState estate
             (scopev, scopet) <- check env' retty (Just TType)
             est <- read estate
             let scopeImps = reverse $ toBind est
             clearEState estate
             -- Bind implicits which were first used in
             -- the argument type 'tyv'
             -- TODO: Also bind the necessary holes for the implicits...
             -- Remember to sort the holes...
             -- This is only in 'PI' implicit mode - it's an error to
             -- have implicits at this level in 'PATT' implicit mode
             let scopev' = bindImplicits 0 scopeImps scopev
             let binder = bindImplicits 0 argImps 
                             (Bind n (Pi info tyv) scopev')
--              putStrLn "CONSTRAINTS AFTER SCOPE"
--              dumpConstraints ctxt ustate

             checkExp loc env binder TType expected

    checkLam : CtxtManage m =>
               annot -> Env Term vars ->
               Name -> (ty : RawImp annot) -> (scope : RawImp annot) ->
               Maybe (Term vars) ->
               ST m (Term vars, Term vars) 
                    [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
    checkLam loc env n ty scope (Just (Bind bn (Pi Explicit pty) psc))
        = do (tyv, tyt) <- check env ty (Just TType)
             weakenEState estate
             (scopev, scopet) <- check (Pi Explicit pty :: env) scope (Just psc)
             clearEState estate
             checkExp loc env (Bind bn (Lam tyv) scopev)
                          (Bind bn (Pi Explicit tyv) scopet)
                          (Just (Bind bn (Pi Explicit pty) psc))
    checkLam loc env n ty scope expected
        = do (tyv, tyt) <- check env ty (Just TType)
             let env' : Env Term (n :: _) = Pi Explicit tyv :: env
             weakenEState estate
             (scopev, scopet) <- check env' scope Nothing
             clearEState estate
             checkExp loc env (Bind n (Lam tyv) scopev)
                          (Bind n (Pi Explicit tyv) scopet)
                          expected
    
    checkLet : CtxtManage m =>
               annot -> Env Term vars ->
               Name -> (val : RawImp annot) -> 
               (ty : RawImp annot) -> (scope : RawImp annot) ->
               Maybe (Term vars) ->
               ST m (Term vars, Term vars) 
                    [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
    checkLet loc env n val ty scope expected
        = do (tyv, tyt) <- check env ty (Just TType)
             (valv, valt) <- check env val (Just tyv)
             let env' : Env Term (n :: _) = Let valv tyv :: env
             weakenEState estate
             (scopev, scopet) <- check env' scope (map weaken expected)
             clearEState estate
             checkExp loc env (Bind n (Let valv tyv) scopev)
                              (Bind n (Let valv tyv) scopet)
                              expected
 
export
inferTerm : CtxtManage m => 
            (ctxt : Var) -> (ustate : Var) -> 
            Env Term vars ->
            (term : RawImp annot) ->
            ST m (Term vars, Term vars) 
                 [ctxt ::: Defs, ustate ::: UState]
inferTerm ctxt ustate env tm
    = do resetHoles ustate
         estate <- new initEState
         (chktm, ty) <- call $ check ctxt ustate estate env tm Nothing
         est <- read estate
         -- Bind the implicits and any unsolved holes they refer to
         -- This is in implicit mode 'PATTERN' and 'PI'
         let fullImps = reverse $ toBind est
         delete estate
--          putStrLn "--- CONSTRAINTS AND HOLES ---"
--          dumpConstraints ctxt ustate
         pure (bindImplicits 0 fullImps chktm, ty)

export
checkTerm : CtxtManage m => 
            (ctxt : Var) -> (ustate : Var) -> 
            Env Term vars ->
            (term : RawImp annot) -> (ty : Term vars) ->
            ST m (Term vars) [ctxt ::: Defs, ustate ::: UState]
checkTerm ctxt ustate env tm ty
    = do resetHoles ustate
         est <- new initEState
         (chktm, ty) <- call $ check ctxt ustate est env tm (Just ty)
         delete est
         dumpConstraints ctxt ustate
         pure chktm

