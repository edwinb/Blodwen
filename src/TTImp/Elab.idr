module TTImp.Elab

import TTImp.TTImp
import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT
import Core.Typecheck
import Core.Unify

import Control.Monad.StateE
import Data.List

%default covering

-- How the elaborator should deal with IBindVar:
-- * NONE: IBindVar is not valid (rhs of an definition, top level expression)
-- * PI: Bind implicits as Pi, in the appropriate scope
-- * PATT: Bind implicits as PVar, but only at the top level
public export
data ImplicitMode = NONE | PI | PATTERN

record ElabState (vars : List Name) where
  constructor MkElabState
  boundNames : List (Name, (Term vars, Term vars))
                  -- implicit pattern/type variable bindings and the 
                  -- term/type they elaborated to
  toBind : List (Name, (Term vars, Term vars))
                  -- implicit pattern/type variables which haven't been
                  -- bound yet

-- A label for the internal elaborator state
data EST : Type where

initEState : ElabState vars
initEState = MkElabState [] []

EState : List Name -> Type
EState = ElabState

-- weaken the unbound implicits which have not yet been bound
weakenEState : CoreM annot [EST ::: EState vs] [EST ::: EState (n :: vs)] ()
weakenEState 
    = do est <- get EST
         putM EST (MkElabState (map wknTms (boundNames est))
                               (map wknTms (toBind est)))
  where
    wknTms : (Name, (Term vs, Term vs)) -> 
             (Name, (Term (n :: vs), Term (n :: vs)))
    wknTms (f, (x, y)) = (f, (weaken x, weaken y))

clearEState : CoreM annot [EST ::: EState (n :: vs)] [EST ::: EState vs] ()
clearEState = putM EST initEState

-- remove the outermost variable from the unbound implicits which have not
-- yet been bound. If it turns out to depend on it, that means it can't
-- be bound at the top level, which is an error.
strengthenEState : (top : Bool) -> annot ->
                   CoreM annot [EST ::: EState (n :: vs)] [EST ::: EState vs] ()
strengthenEState True loc = clearEState
strengthenEState False loc
    = do est <- get EST
         bns <- traverse (\x => strTms x) (boundNames est)
         todo <- traverse (\x => strTms x) (toBind est)
         putM EST (MkElabState bns todo)
  where
    strTms : (Name, (Term (n :: vs), Term (n :: vs))) -> 
             Core annot [EST ::: EState (n :: vs)] (Name, (Term vs, Term vs))
    strTms (f, (x, y))
        = case (shrinkTerm x (DropCons SubRefl),
                  shrinkTerm y (DropCons SubRefl)) of
               (Just x', Just y') => pure (f, (x', y'))
               _ => throw (GenericMsg loc ("Invalid unbound implicit " ++ show f))

clearToBind : CoreM annot [EST ::: EState vs] [EST ::: EState vs] ()
clearToBind = 
    do est <- get EST
       putM EST (record { toBind = [] } est)
   
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

convert : annot ->
          Env Term vars ->
          Term vars -> Term vars -> 
          Core annot 
               [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
               (List Name)
convert loc env x y 
    = catch (do vs <- unify loc env x y
                solveConstraints
                pure vs)
            (\err => do gam <- getCtxt 
                        throw (WhenUnifying loc (normaliseHoles gam env x)
                                                (normaliseHoles gam env y)
                                  err))

checkExp : annot ->
           Env Term vars ->
           (term : Term vars) -> (got : Term vars) -> 
           (exp : Maybe (Term vars)) ->
           Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                (Term vars, Term vars) 
checkExp loc env tm got Nothing
    = pure (tm, got)
checkExp loc env tm got (Just exp) 
    = do constr <- convert loc env got exp
         case constr of
              [] => pure (tm, got)
              cs => do gam <- getCtxt
                       c <- addConstant env tm exp cs
                       pure (mkConstantApp c env, got)

inventFnType : Env Term vars ->
               (bname : Name) ->
               Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                    (Term vars, Term (bname :: vars))
inventFnType env bname
    = do an <- genName "argh"
         scn <- genName "sch"
         let argTy = mkConstantApp an env
         let scTy = mkConstantApp scn (Pi Explicit argTy :: env)
         pure (argTy, scTy)

mutual
  check : (top : Bool) -> -- top level, unbound implicits bound here
          Env Term vars ->
          (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
          Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
               (Term vars, Term vars) 
  check top env tm exp = checkImp top env (insertImpLam env tm exp) exp

  insertImpLam : Env Term vars ->
                 (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
                 RawImp annot
  insertImpLam env tm Nothing = tm
  insertImpLam env tm (Just ty) = tm -- TODO

  checkImp : (top : Bool) -> -- top level, unbound implicits bound here
             Env Term vars ->
             (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
             Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                  (Term vars, Term vars) 
  checkImp top env (IVar loc x) expected 
      = do (x', varty) <- infer loc env (RVar x)
           gam <- getCtxt
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
           gam <- getCtxt
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
                  do bn <- genName "aTy"
                     (expty, scty) <- inventFnType env bn
                     (argtm, argty) <- 
                         check top env arg (Just (Bind bn (Pi Explicit expty) scty))
                     checkExp loc env (App fntm argtm)
                                  (Bind bn (Let argtm argty) scty) expected
  checkImp top env (IPrimVal loc x) expected 
      = do (x', ty) <- infer loc env (RPrimVal x)
           checkExp loc env x' ty expected
  checkImp top env (IType loc) exp
      = checkExp loc env TType TType exp
  checkImp top env (IBindVar loc n) Nothing
      = do t <- addHole env TType
           let hty = mkConstantApp t env
           est <- get EST
           case lookup n (boundNames est) of
                Nothing =>
                  do tm <- addBoundName n env hty
                     put EST 
                         (record { boundNames $= ((n, (tm, hty)) ::),
                                   toBind $= ((n, (tm, hty)) ::) } est)
                     pure (tm, hty)
                Just (tm, ty) =>
                     pure (tm, ty)
  checkImp top env (IBindVar loc n) (Just expected) 
      = do est <- get EST
           case lookup n (boundNames est) of
                Nothing =>
                  do tm <- addBoundName n env expected
                     putStrLn $ "ADDED BOUND IMPLICIT " ++ show (n, (tm, expected))
                     put EST 
                         (record { boundNames $= ((n, (tm, expected)) ::),
                                   toBind $= ((n, (tm, expected)) :: ) } est)
                     pure (tm, expected)
                Just (tm, ty) =>
                     checkExp loc env tm ty (Just expected)
  checkImp top env (Implicit loc) Nothing
      = do t <- addHole env TType
           let hty = mkConstantApp t env
           n <- addHole env hty
           pure (mkConstantApp n env, hty)
  checkImp top env (Implicit loc) (Just expected) 
      = do n <- addHole env expected
           pure (mkConstantApp n env, expected)
 
  -- Get the implicit arguments that need to be inserted at this point
  -- in a function application. Do this by reading off implicit Pis
  -- in the expected type ('ty') and adding new holes for each.
  -- Return the (normalised) remainder of the type, and the list of
  -- implicits added
  getImps : annot -> Env Term vars ->
            (ty : NF vars) -> List (Term vars) ->
            Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                 (NF vars, List (Term vars)) 
  getImps loc env (NBind _ (Pi Implicit ty) sc) imps
      = do n <- addHole env (quote empty env ty)
           let arg = mkConstantApp n env
           getImps loc env (sc (toClosure env arg)) (arg :: imps)
  getImps loc env ty imps = pure (ty, reverse imps)

  checkPi : (top : Bool) -> -- top level, unbound implicits bound here
            annot -> Env Term vars ->
            PiInfo -> Name -> 
            (argty : RawImp annot) -> (retty : RawImp annot) ->
            Maybe (Term vars) ->
            Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                 (Term vars, Term vars) 
  checkPi top loc env info n argty retty expected
      = do (tyv, tyt) <- check False env argty (Just TType)
           let env' : Env Term (n :: _) = Pi info tyv :: env
           est <- get EST
           let argImps = reverse $ toBind est
           clearToBind 
           weakenEState 
           (scopev, scopet) <- check top env' retty (Just TType)
           est <- get EST
           let scopeImps = reverse $ toBind est
           strengthenEState top loc
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

  checkLam : (top : Bool) -> -- top level, unbound implicits bound here
             annot -> Env Term vars ->
             Name -> (ty : RawImp annot) -> (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                  (Term vars, Term vars) 
  checkLam top loc env n ty scope (Just (Bind bn (Pi Explicit pty) psc))
      = do (tyv, tyt) <- check top env ty (Just TType)
           weakenEState
           (scopev, scopet) <- check top (Pi Explicit pty :: env) scope (Just psc)
           strengthenEState top loc
           checkExp loc env (Bind bn (Lam tyv) scopev)
                        (Bind bn (Pi Explicit tyv) scopet)
                        (Just (Bind bn (Pi Explicit pty) psc))
  checkLam top loc env n ty scope expected
      = do (tyv, tyt) <- check top env ty (Just TType)
           let env' : Env Term (n :: _) = Pi Explicit tyv :: env
           weakenEState
           (scopev, scopet) <- check top env' scope Nothing
           strengthenEState top loc
           checkExp loc env (Bind n (Lam tyv) scopev)
                        (Bind n (Pi Explicit tyv) scopet)
                        expected
  
  checkLet : (top : Bool) -> -- top level, unbound implicits bound here
             annot -> Env Term vars ->
             Name -> (val : RawImp annot) -> 
             (ty : RawImp annot) -> (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                  (Term vars, Term vars) 
  checkLet top loc env n val ty scope expected
      = do (tyv, tyt) <- check top env ty (Just TType)
           (valv, valt) <- check top env val (Just tyv)
           let env' : Env Term (n :: _) = Let valv tyv :: env
           weakenEState
           (scopev, scopet) <- check top env' scope (map weaken expected)
           strengthenEState top loc
           checkExp loc env (Bind n (Let valv tyv) scopev)
                            (Bind n (Let valv tyv) scopet)
                            expected

-- Find any holes in the resulting expression, and implicitly bind them
-- at the top level (i.e. they can't depend on any explicitly given
-- arguments).
findHoles : Term vars ->
            Core annot [Ctxt ::: Defs, UST ::: UState annot]
                 (Term vars) 
findHoles tm
    = do new HVar []
         tm <- holes tm
         hs <- get HVar
         delete HVar
         pure (bindTopImplicits (reverse hs) tm)
  where
    data HVar : Type where

    mkType : (vars : List Name) -> Term hs -> Maybe (Term hs)
    mkType (v :: vs) (Bind tm (Pi _ ty) sc) 
        = do sc' <- mkType vs sc
             shrinkTerm sc' (DropCons SubRefl)
    mkType _ tm = pure tm

    processHole : Name -> (vars : List Name) -> ClosedTerm ->
                  Core annot [HVar ::: List (Name, ClosedTerm),
                        Ctxt ::: Defs, UST ::: UState annot]
                       ()
    processHole n vars ty
       = do hs <- get HVar
--             putStrLn $ "IMPLICIT: " ++ show (n, vars, ty)
            case mkType vars ty of
                 Nothing => pure ()
                 Just impTy =>
                    case lookup n hs of
                         Just _ => pure ()
                         Nothing => put HVar ((n, impTy) :: hs)

    holes : Term vars -> 
            Core annot [HVar ::: List (Name, ClosedTerm),
                  Ctxt ::: Defs, UST ::: UState annot]
                 (Term vars)
    holes {vars} (Ref nt fn) 
        = do gam <- getCtxt
             case lookupDefTy fn gam of
                  Just (Hole, ty) =>
                       do processHole fn vars ty
                          pure (Ref nt fn)
                  _ => pure (Ref nt fn)
    holes (App fn arg)
        = do fn' <- holes fn
             arg' <- holes arg
             pure (App fn' arg')
    -- Allow implicits under 'Pi' and 'PVar' only
    holes (Bind y (Pi imp ty) sc)
        = do ty' <- holes ty
             sc' <- holes sc
             pure (Bind y (Pi imp ty') sc')
    holes (Bind y (PVar ty) sc)
        = do ty' <- holes ty
             sc' <- holes sc
             pure (Bind y (PVar ty') sc')
    holes tm = pure tm
                                      

export
inferTerm : Env Term vars ->
            (term : RawImp annot) ->
            Core annot [Ctxt ::: Defs, UST ::: UState annot]
                 (Term vars, Term vars) 
inferTerm env tm
    = do resetHoles
         new EST initEState
         (chktm, ty) <- call $ check True env tm Nothing
         est <- get EST
         -- Bind the implicits and any unsolved holes they refer to
         -- This is in implicit mode 'PATTERN' and 'PI'
         let fullImps = reverse $ toBind est
         delete EST
         putStrLn "--- CONSTRAINTS AND HOLES ---"
         dumpConstraints 
         let restm = bindImplicits 0 (dropSnd fullImps) chktm
         gam <- getCtxt
         -- TODO: Only in implicits mode, and normalise only the hole names
         hs <- findHoles (normalise gam env restm)
--          putStrLn $ "Extra implicits: " ++ show hs
         pure (restm, ty)

export
checkTerm : Env Term vars ->
            (term : RawImp annot) -> (ty : Term vars) ->
            Core annot [Ctxt ::: Defs, UST ::: UState annot]
                 (Term vars) 
checkTerm env tm ty
    = do resetHoles
         new EST initEState
         (chktm, ty) <- call $ check True env tm (Just ty)
         delete EST
         dumpConstraints
         pure chktm

