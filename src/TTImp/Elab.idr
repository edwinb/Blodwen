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

-- weaken the unbound implicits which have not yet been bound
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

-- remove the outermost variable from the unbound implicits which have not
-- yet been bound. If it turns out to depend on it, that means it can't
-- be bound at the top level, which is an error.
strengthenEState : CtxtManage m =>
                   (estate : Var) ->
                   (top : Bool) ->
                   ST m () [estate ::: EState (n :: vs) :-> EState vs]
strengthenEState {m} estate True = clearEState estate
strengthenEState {m} estate False
    = do est <- read estate
         bns <- mapST strTms (boundNames est)
         todo <- mapST strTms (toBind est)
         write estate (MkElabState bns todo)
  where
    strTms : (Name, (Term (n :: vs), Term (n :: vs))) -> 
             ST m (Name, (Term vs, Term vs))
                  [estate ::: EState (n :: vs)]
    strTms (f, (x, y))
        = case (shrinkTerm x (DropCons SubRefl),
                  shrinkTerm y (DropCons SubRefl)) of
               (Just x', Just y') => pure (f, (x', y'))
               _ => throw (GenericMsg ("Invalid unbound implicit " ++ show f))

clearToBind : (estate : Var) ->
              ST m () [estate ::: EState vs :-> EState vs]
clearToBind estate = 
    do est <- read estate
       write estate (record { toBind = [] } est)
   
dropSnd : List (a, (b, c)) -> List (a, c)
dropSnd = map (\ (n, (_, t)) => (n, t))

-- TODO: Needs to return the type, and deal with pattern implicits
-- differently because that affects the type
bindImplicits : Int -> 
                List (Name, Term vars) ->
                Term vars -> Term vars
bindImplicits i [] scope = scope
bindImplicits i ((n, ty) :: imps) scope
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

bindTopImplicits : List (Name, ClosedTerm) -> Term vars -> Term vars
bindTopImplicits {vars} hs tm
    = bindImplicits 0 (map weakenVars hs) tm
  where
    weakenVars : (Name, ClosedTerm) -> (Name, Term vars)
    weakenVars (n, tm) = (n, rewrite sym (appendNilRightNeutral vars) in
                                     weakenNs vars tm)

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
            (top : Bool) -> -- top level, unbound implicits bound here
            Env Term vars ->
            (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
            ST m (Term vars, Term vars) 
                 [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
    check top env tm exp = checkImp top env (insertImpLam env tm exp) exp

    insertImpLam : Env Term vars ->
                   (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
                   RawImp annot
    insertImpLam env tm Nothing = tm
    insertImpLam env tm (Just ty) = tm -- TODO

    checkImp : CtxtManage m =>
               (top : Bool) -> -- top level, unbound implicits bound here
               Env Term vars ->
               (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
               ST m (Term vars, Term vars) 
                    [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
    checkImp top env (IVar loc x) expected 
        = do (x', varty) <- infer ctxt env (RVar x)
             gam <- getCtxt ctxt
             -- If the variable has an implicit binder in its type, add
             -- the implicits here
             (ty, imps) <- getImps loc env (nf gam env varty) []
             checkExp loc env (apply x' imps) (quote empty env ty) expected
    checkImp top env (IPi loc plicity n ty retTy) expected 
        = checkPi top loc env plicity n ty retTy expected
    checkImp top env (ILam loc n ty scope) expected
        = checkLam top loc env n ty scope expected
    checkImp top env (ILet loc n nTy nVal scope) expected 
        = checkLet top loc env n nTy nVal scope expected
    checkImp top env (IApp loc fn arg) expected 
        = do (fntm, fnty) <- check top env fn Nothing
             gam <- getCtxt ctxt
             -- If the function has an implicit binder in its type, add
             -- the implicits here
             (scopeTy, impArgs) <- getImps loc env (nf gam env fnty) []
             case scopeTy of
                  NBind _ (Pi _ ty) scdone =>
                    do (argtm, argty) <- check top env arg (Just (quote empty env ty))
                       let sc' = scdone (toClosure env argtm)
                       checkExp loc env (App (apply fntm impArgs) argtm)
                                    (quote gam env sc') expected
                  _ => 
                    do bn <- genName ustate "aTy"
                       (expty, scty) <- inventFnType env bn
                       (argtm, argty) <- 
                           check top env arg (Just (Bind bn (Pi Explicit expty) scty))
                       checkExp loc env (App fntm argtm)
                                    (Bind bn (Let argtm argty) scty) expected
    checkImp top env (IPrimVal loc x) expected 
        = do (x', ty) <- infer ctxt env (RPrimVal x)
             checkExp loc env x' ty expected
    checkImp top env (IType loc) exp
        = checkExp loc env TType TType exp
    checkImp top env (IBindVar loc n) Nothing
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
    checkImp top env (IBindVar loc n) (Just expected) 
        = do est <- read estate
             case lookup n (boundNames est) of
                  Nothing =>
                    do tm <- addBoundName ctxt ustate n env expected
--                        putStrLn $ "ADDED BOUND IMPLICIT " ++ show (n, (tm, expected))
                       write estate 
                           (record { boundNames $= ((n, (tm, expected)) ::),
                                     toBind $= ((n, (tm, expected)) :: ) } est)
                       pure (tm, expected)
                  Just (tm, ty) =>
                       checkExp loc env tm ty (Just expected)
    checkImp top env (Implicit loc) Nothing
        = do t <- addHole ctxt ustate env TType
             let hty = mkConstantApp t env
             n <- addHole ctxt ustate env hty
             pure (mkConstantApp n env, hty)
    checkImp top env (Implicit loc) (Just expected) 
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
              (top : Bool) -> -- top level, unbound implicits bound here
              annot -> Env Term vars ->
              PiInfo -> Name -> 
              (argty : RawImp annot) -> (retty : RawImp annot) ->
              Maybe (Term vars) ->
              ST m (Term vars, Term vars) 
                   [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
    checkPi top loc env info n argty retty expected
        = do (tyv, tyt) <- check False env argty (Just TType)
             let env' : Env Term (n :: _) = Pi info tyv :: env
             est <- read estate
             let argImps = reverse $ toBind est
             clearToBind estate
             weakenEState estate
             (scopev, scopet) <- check top env' retty (Just TType)
             est <- read estate
             let scopeImps = reverse $ toBind est
             strengthenEState estate top
             -- Bind implicits which were first used in
             -- the argument type 'tyv'
             -- TODO: This is only in 'PI' implicit mode - it's an error to
             -- have implicits at this level in 'PATT' implicit mode
             if top
                then do let scopev' = bindImplicits 0 (dropSnd scopeImps) scopev
                        let binder = bindImplicits 0 (dropSnd argImps)
                                        (Bind n (Pi info tyv) scopev')
                        checkExp loc env binder TType expected
                else checkExp loc env (Bind n (Pi info tyv) scopev)
                                      TType expected

    checkLam : CtxtManage m =>
               (top : Bool) -> -- top level, unbound implicits bound here
               annot -> Env Term vars ->
               Name -> (ty : RawImp annot) -> (scope : RawImp annot) ->
               Maybe (Term vars) ->
               ST m (Term vars, Term vars) 
                    [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
    checkLam top loc env n ty scope (Just (Bind bn (Pi Explicit pty) psc))
        = do (tyv, tyt) <- check top env ty (Just TType)
             weakenEState estate
             (scopev, scopet) <- check top (Pi Explicit pty :: env) scope (Just psc)
             strengthenEState estate top
             checkExp loc env (Bind bn (Lam tyv) scopev)
                          (Bind bn (Pi Explicit tyv) scopet)
                          (Just (Bind bn (Pi Explicit pty) psc))
    checkLam top loc env n ty scope expected
        = do (tyv, tyt) <- check top env ty (Just TType)
             let env' : Env Term (n :: _) = Pi Explicit tyv :: env
             weakenEState estate
             (scopev, scopet) <- check top env' scope Nothing
             strengthenEState estate top
             checkExp loc env (Bind n (Lam tyv) scopev)
                          (Bind n (Pi Explicit tyv) scopet)
                          expected
    
    checkLet : CtxtManage m =>
               (top : Bool) -> -- top level, unbound implicits bound here
               annot -> Env Term vars ->
               Name -> (val : RawImp annot) -> 
               (ty : RawImp annot) -> (scope : RawImp annot) ->
               Maybe (Term vars) ->
               ST m (Term vars, Term vars) 
                    [ctxt ::: Defs, ustate ::: UState, estate ::: EState vars]
    checkLet top loc env n val ty scope expected
        = do (tyv, tyt) <- check top env ty (Just TType)
             (valv, valt) <- check top env val (Just tyv)
             let env' : Env Term (n :: _) = Let valv tyv :: env
             weakenEState estate
             (scopev, scopet) <- check top env' scope (map weaken expected)
             strengthenEState estate top
             checkExp loc env (Bind n (Let valv tyv) scopev)
                              (Bind n (Let valv tyv) scopet)
                              expected

-- Find any holes in the resulting expression, and implicitly bind them
-- at the top level (i.e. they can't depend on any explicitly given
-- arguments).
findHoles : CtxtManage m =>
            (ctxt : Var) -> (ustate : Var) ->
            Term vars ->
            ST m (Term vars) [ctxt ::: Defs, ustate ::: UState]
findHoles ctxt ustate tm
    = do hvar <- new []
         tm <- holes hvar tm
         hs <- read hvar
         delete hvar
         pure (bindTopImplicits (reverse hs) tm)
  where
    mkType : (vars : List Name) -> Term hs -> Maybe (Term hs)
    mkType (v :: vs) (Bind tm (Pi _ ty) sc) 
        = do sc' <- mkType vs sc
             shrinkTerm sc' (DropCons SubRefl)
    mkType _ tm = pure tm

    processHole : CtxtManage m =>
                  (hvar : Var) -> Name -> (vars : List Name) -> ClosedTerm ->
                  ST m () [hvar ::: State (List (Name, ClosedTerm)),
                           ctxt ::: Defs, ustate ::: UState]
    processHole hvar n vars ty
       = do hs <- read hvar
--             putStrLn $ "IMPLICIT: " ++ show (n, vars, ty)
            case mkType vars ty of
                 Nothing => pure ()
                 Just impTy =>
                    case lookup n hs of
                         Just _ => pure ()
                         Nothing => write hvar ((n, impTy) :: hs)

    holes : CtxtManage m =>
            (hvar : Var) -> Term vars -> 
            ST m (Term vars) [hvar ::: State (List (Name, ClosedTerm)),
                     ctxt ::: Defs, ustate ::: UState]
    holes {vars} hvar (Ref nt fn) 
        = do gam <- getCtxt ctxt
             case lookupDefTy fn gam of
                  Just (Hole, ty) =>
                       do processHole hvar fn vars ty
                          pure (Ref nt fn)
                  _ => pure (Ref nt fn)
    holes hvar (App fn arg)
        = do fn' <- holes hvar fn
             arg' <- holes hvar arg
             pure (App fn' arg')
    -- Allow implicits under 'Pi' and 'PVar' only
    holes hvar (Bind y (Pi imp ty) sc)
        = do ty' <- holes hvar ty
             sc' <- holes hvar sc
             pure (Bind y (Pi imp ty') sc')
    holes hvar (Bind y (PVar ty) sc)
        = do ty' <- holes hvar ty
             sc' <- holes hvar sc
             pure (Bind y (PVar ty') sc')
    holes hvar tm = pure tm
                                      

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
         (chktm, ty) <- call $ check ctxt ustate estate True env tm Nothing
         est <- read estate
         -- Bind the implicits and any unsolved holes they refer to
         -- This is in implicit mode 'PATTERN' and 'PI'
         let fullImps = reverse $ toBind est
         delete estate
         putStrLn "--- CONSTRAINTS AND HOLES ---"
         dumpConstraints ctxt ustate
         let restm = bindImplicits 0 (dropSnd fullImps) chktm
         gam <- getCtxt ctxt
         -- TODO: Only in implicits mode, and normalise only the hole names
         hs <- findHoles ctxt ustate (normalise gam env restm)
--          putStrLn $ "Extra implicits: " ++ show hs
         pure (restm, ty)

export
checkTerm : CtxtManage m => 
            (ctxt : Var) -> (ustate : Var) -> 
            Env Term vars ->
            (term : RawImp annot) -> (ty : Term vars) ->
            ST m (Term vars) [ctxt ::: Defs, ustate ::: UState]
checkTerm ctxt ustate env tm ty
    = do resetHoles ustate
         est <- new initEState
         (chktm, ty) <- call $ check ctxt ustate est True env tm (Just ty)
         delete est
         dumpConstraints ctxt ustate
         pure chktm

