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
-- * PI True: Bind implicits as Pi, in the appropriate scope, and bind
--            any additional holes
-- * PI False: As above, but don't bind additional holes
-- * PATTERN: Bind implicits as PVar, but only at the top level
public export
data ImplicitMode = NONE | PI Bool | PATTERN

record ElabState (vars : List Name) where
  constructor MkElabState
  boundNames : List (Name, (Term vars, Term vars))
                  -- implicit pattern/type variable bindings and the 
                  -- term/type they elaborated to
  toBind : List (Name, (Term vars, Term vars))
                  -- implicit pattern/type variables which haven't been
                  -- bound yet. 

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
    -- Remove any instance of the top level local variable from an
    -- application. Fail if it turns out to be necessary.
    -- NOTE: While this isn't strictly correct given the type of the hole
    -- which stands for the unbound implicits, it's harmless because we
    -- never actualy *use* that hole - this process is only to ensure that the
    -- unbound implicit doesn't depend on any variables it doesn't have
    -- in scope.
    removeArgVars : List (Term (n :: vs)) -> Maybe (List (Term vs))
    removeArgVars [] = pure []
    removeArgVars (Local (There p) :: args) 
        = do args' <- removeArgVars args
             pure (Local p :: args')
    removeArgVars (Local Here :: args) 
        = removeArgVars args
    removeArgVars (a :: args)
        = do a' <- shrinkTerm a (DropCons SubRefl)
             args' <- removeArgVars args
             pure (a' :: args')

    removeArg : Term (n :: vs) -> Maybe (Term vs)
    removeArg tm with (unapply tm)
      removeArg (apply f args) | ArgsList 
          = do args' <- removeArgVars args
               f' <- shrinkTerm f (DropCons SubRefl)
               pure (apply f' args')

    strTms : (Name, (Term (n :: vs), Term (n :: vs))) -> 
             Core annot [EST ::: EState (n :: vs)] (Name, (Term vs, Term vs))
    strTms {vs} (f, (x, y))
        = case (removeArg x, shrinkTerm y (DropCons SubRefl)) of
               (Just x', Just y') => pure (f, (x', y'))
               _ => throw (GenericMsg loc ("Invalid unbound implicit " ++ show f))

clearToBind : CoreM annot [EST ::: EState vs] [EST ::: EState vs] ()
clearToBind = 
    do est <- get EST
--        putStrLn $ "Clearing holes: " ++ show (map fst (toBind est))
       putM EST (record { toBind = [] } est)
   
dropTmIn : List (a, (c, d)) -> List (a, d)
dropTmIn = map (\ (n, (_, t)) => (n, t))

-- Bind implicit arguments, returning the new term and its updated type
bindImplVars : Int -> 
               ImplicitMode ->
               Gamma ->
               List (Name, Term vars) ->
               Term vars -> Term vars -> (Term vars, Term vars)
bindImplVars i NONE gam args scope scty = (scope, scty)
bindImplVars i mode gam [] scope scty = (scope, scty)
bindImplVars i mode gam ((n, ty) :: imps) scope scty
    = let (scope', ty') = bindImplVars (i + 1) mode gam imps scope scty
          tmpN = MN "unb" i
          repNameTm = repName (Ref Bound tmpN) scope' 
          repNameTy = repName (Ref Bound tmpN) ty' in
          case mode of
               PATTERN =>
                   (Bind n (PVar ty) (refToLocal tmpN n repNameTm), 
                    Bind n (PVTy ty) (refToLocal tmpN n repNameTy))
               _ => (Bind n (Pi Implicit ty) (refToLocal tmpN n repNameTm), ty')
  where
    -- Replace the name applied to the given number of arguments 
    -- with another term
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
                        Just Refl => 
                           let locs = case lookupDef fn' gam of
                                           Just (Hole i) => i
                                           _ => 0
                                        in
                               apply new (drop locs (getArgs (App fn arg)))
               _ => App (repName new fn) (repName new arg)
    repName new (PrimVal y) = PrimVal y
    repName new Erased = Erased
    repName new TType = TType

bindImplicits : ImplicitMode ->
                Gamma -> Env Term vars ->
                List (Name, Term vars) ->
                Term vars -> Term vars -> (Term vars, Term vars)
bindImplicits mode gam env hs tm ty 
   = bindImplVars 0 mode gam hs (normaliseHoles gam env tm)
                                (normaliseHoles gam env ty)

bindTopImplicits : ImplicitMode -> Gamma -> Env Term vars ->
                   List (Name, ClosedTerm) -> Term vars -> Term vars ->
                   (Term vars, Term vars)
bindTopImplicits {vars} mode gam env hs tm ty
    = bindImplicits mode gam env (map weakenVars hs) tm ty
  where
    weakenVars : (Name, ClosedTerm) -> (Name, Term vars)
    weakenVars (n, tm) = (n, rewrite sym (appendNilRightNeutral vars) in
                                     weakenNs vars tm)

convert : annot ->
          Env Term vars ->
          NF vars -> NF vars -> 
          Core annot 
               [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
               (List Name)
convert loc env x y 
    = catch (do solveConstraints
                vs <- unify loc env x y
                solveConstraints
                pure vs)
            (\err => do gam <- getCtxt 
                        throw (WhenUnifying loc (quote empty env x) -- (normaliseHoles gam env x)
                                                (quote empty env y) -- (normaliseHoles gam env y)
                                  err))
  
-- Get the implicit arguments that need to be inserted at this point
-- in a function application. Do this by reading off implicit Pis
-- in the expected type ('ty') and adding new holes for each.
-- Return the (normalised) remainder of the type, and the list of
-- implicits added
getImps : annot -> Env Term vars ->
          (ty : NF vars) -> List (Term vars) ->
          Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
               (NF vars, List (Term vars)) 
getImps loc env (NBind bn (Pi Implicit ty) sc) imps
    = do hn <- genName (nameRoot bn)
         addNamedHole hn env (quote empty env ty)
         let arg = mkConstantApp hn env
         getImps loc env (sc (toClosure env arg)) (arg :: imps)
getImps loc env ty imps = pure (ty, reverse imps)

  
-- When converting, add implicits until we've applied enough for the
-- expected type
convertImps : annot -> Env Term vars ->
              (got : NF vars) -> (exp : NF vars) -> List (Term vars) ->
              Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                         (NF vars, List (Term vars))
convertImps loc env (NBind bn (Pi Implicit ty) sc) (NBind bn' (Pi Implicit ty') sc') imps
    = pure (NBind bn (Pi Implicit ty) sc, reverse imps)
convertImps loc env (NBind bn (Pi Implicit ty) sc) exp imps
    = do hn <- genName (nameRoot bn)
         addNamedHole hn env (quote empty env ty)
         let arg = mkConstantApp hn env
         convertImps loc env (sc (toClosure env arg)) exp (arg :: imps)
convertImps loc env got exp imps = pure (got, reverse imps)

checkExp : annot ->
           Env Term vars ->
           (term : Term vars) -> (got : Term vars) -> 
           (exp : Maybe (Term vars)) ->
           Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                (Term vars, Term vars) 
checkExp loc env tm got Nothing
    = pure (tm, got)
checkExp loc env tm got (Just exp) 
    = do gam <- getCtxt
         let expnf = nf gam env exp
         (got', imps) <- convertImps loc env (nf gam env got) expnf []
         constr <- convert loc env got' expnf
         case constr of
              [] => pure (apply tm imps, quote empty env got')
              cs => do gam <- getCtxt
                       c <- addConstant env (apply tm imps) exp cs
                       pure (mkConstantApp c env, quote empty env got')

inventFnType : Env Term vars ->
               (bname : Name) ->
               Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                    (Term vars, Term (bname :: vars))
inventFnType env bname
    = do an <- genName "argh"
         scn <- genName "sch"
         argTy <- addBoundName an env TType
         scTy <- addBoundName scn (Pi Explicit argTy :: env) TType
         pure (argTy, scTy)

mutual
  check : (top : Bool) -> -- top level, unbound implicits bound here
          ImplicitMode ->
          Env Term vars ->
          (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
          Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
               (Term vars, Term vars) 
  check top impmode env tm exp 
      = let tm' = insertImpLam env tm exp in
            checkImp top impmode env tm' exp

  insertImpLam : Env Term vars ->
                 (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
                 RawImp annot
  insertImpLam env tm Nothing = tm
  insertImpLam env tm (Just ty) = bindLam tm ty
    where
      bindLam : RawImp annot -> Term vars -> RawImp annot
      bindLam tm (Bind n (Pi Implicit ty) sc)
          = let loc = getAnnot tm in
                ILam loc Implicit n (Implicit loc) (bindLam tm sc)
      bindLam tm sc = tm

  checkImp : (top : Bool) -> -- top level, unbound implicits bound here
             ImplicitMode ->
             Env Term vars ->
             (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
             Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                  (Term vars, Term vars) 
  checkImp top impmode env (IVar loc x) expected 
      = do (x', varty) <- infer loc env (RVar x)
           gam <- getCtxt
           checkExp loc env x' varty expected
  checkImp top impmode env (IPi loc plicity Nothing ty retTy) expected 
      = do n <- genName "pi"
           checkPi top impmode loc env plicity n ty retTy expected
  checkImp top impmode env (IPi loc plicity (Just n) ty retTy) expected 
      = checkPi top impmode loc env plicity n ty retTy expected
  checkImp top impmode env (ILam loc plicity n ty scope) expected
      = checkLam top impmode loc env plicity n ty scope expected
  checkImp top impmode env (ILet loc n nTy nVal scope) expected 
      = checkLet top impmode loc env n nTy nVal scope expected
  checkImp top impmode env (IApp loc fn arg) expected 
      = do (fntm, fnty) <- check top impmode env fn Nothing
           gam <- getCtxt
           -- If the function has an implicit binder in its type, add
           -- the implicits here
           (scopeTy, impArgs) <- getImps loc env (nf gam env fnty) []
           case scopeTy of
                NBind _ (Pi _ ty) scdone =>
                  do (argtm, argty) <- check top impmode env arg (Just (quote empty env ty))
                     let sc' = scdone (toClosure env argtm)
                     checkExp loc env (App (apply fntm impArgs) argtm)
                                  (quote gam env sc') expected
                _ => 
                  do bn <- genName "aTy"
                     -- invent names for the argument and return types
                     (expty, scty) <- inventFnType env bn
                     -- Check the argument type against the invented arg type
                     (argtm, argty) <- 
                         check top impmode env arg (Just expty) -- (Bind bn (Pi Explicit expty) scty))
                     -- Check the type of 'fn' is an actual function type
                     (fnchk, _) <-
                         checkExp loc env fntm 
                                  (Bind bn (Pi Explicit expty) scty) 
                                  (Just (quote gam env scopeTy))
                     checkExp loc env (App fnchk argtm)
                                  (Bind bn (Let argtm argty) scty) expected
  checkImp top impmode env (IPrimVal loc x) expected 
      = do (x', ty) <- infer loc env (RPrimVal x)
           checkExp loc env x' ty expected
  checkImp top impmode env (IType loc) exp
      = checkExp loc env TType TType exp
  checkImp top impmode env (IBindVar loc str) Nothing
      = do let n = PV str
           t <- addHole env TType
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
  checkImp top impmode env (IBindVar loc str) (Just expected) 
      = do let n = PV str
           est <- get EST
           case lookup n (boundNames est) of
                Nothing =>
                  do tm <- addBoundName n env expected
--                      putStrLn $ "ADDED BOUND IMPLICIT " ++ show (n, (tm, expected))
                     put EST 
                         (record { boundNames $= ((n, (tm, expected)) ::),
                                   toBind $= ((n, (tm, expected)) :: ) } est)
                     pure (tm, expected)
                Just (tm, ty) =>
                     checkExp loc env tm ty (Just expected)
  checkImp top impmode env (Implicit loc) Nothing
      = do t <- addHole env TType
           let hty = mkConstantApp t env
           n <- addHole env hty
           pure (mkConstantApp n env, hty)
  checkImp top impmode env (Implicit loc) (Just expected) 
      = do n <- addHole env expected
           pure (mkConstantApp n env, expected)
 
  checkPi : (top : Bool) -> -- top level, unbound implicits bound here
            ImplicitMode ->
            annot -> Env Term vars -> PiInfo -> Name -> 
            (argty : RawImp annot) -> (retty : RawImp annot) ->
            Maybe (Term vars) ->
            Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                 (Term vars, Term vars) 
  checkPi top impmode loc env info n argty retty expected
      = do (tyv, tyt) <- check False impmode env argty (Just TType)
           let env' : Env Term (n :: _) = Pi info tyv :: env
           est <- get EST
           let argImps = if top then (reverse $ toBind est) else []
           when top $ clearToBind 
           weakenEState 
           (scopev, scopet) <- check top impmode env' retty (Just TType)
           est <- get EST
           let scopeImps = reverse $ toBind est
           strengthenEState top loc
           -- Bind implicits which were first used in
           -- the argument type 'tyv'
           -- This is only in 'PI' implicit mode - it's an error to
           -- have implicits at this level in 'PATT' implicit mode
           case (top, impmode) of
                (True, PI _) =>
                   do -- putStrLn $ "Binding implicits " ++ show (dropTmIn argImps)
                      --                                 ++ show (dropTmIn scopeImps)
                      gam <- getCtxt
                      let (scopev', scopet')
                          = bindImplicits impmode gam env'
                                          (dropTmIn scopeImps) scopev scopet
                      let (binder, bindert)
                          = bindImplicits impmode gam env
                                          (dropTmIn argImps)
                                          (Bind n (Pi info tyv) scopev')
                                          TType
                      traverse (\n => implicitBind n) (map fst scopeImps)
                      traverse (\n => implicitBind n) (map fst argImps)
                      checkExp loc env binder bindert expected
                _ => checkExp loc env (Bind n (Pi info tyv) scopev)
                                      TType expected

  checkLam : (top : Bool) -> -- top level, unbound implicits bound here
             ImplicitMode ->
             annot -> Env Term vars -> PiInfo -> Name ->
             (ty : RawImp annot) -> (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                  (Term vars, Term vars) 
  checkLam top impmode loc env plicity n ty scope (Just (Bind bn (Pi Explicit pty) psc))
      = do (tyv, tyt) <- check top impmode env ty (Just TType)
           weakenEState
           (scopev, scopet) <- check top impmode (Pi plicity pty :: env) scope 
                                     (Just (renameTop n psc))
           strengthenEState top loc
           checkExp loc env (Bind n (Lam plicity tyv) scopev)
                        (Bind n (Pi plicity tyv) scopet)
                        (Just (Bind bn (Pi plicity pty) psc))
  checkLam top impmode loc env plicity n ty scope expected
      = do (tyv, tyt) <- check top impmode env ty (Just TType)
           let env' : Env Term (n :: _) = Pi Explicit tyv :: env
           weakenEState
           (scopev, scopet) <- check top impmode env' scope Nothing
           strengthenEState top loc
           checkExp loc env (Bind n (Lam plicity tyv) scopev)
                        (Bind n (Pi plicity tyv) scopet)
                        expected
  
  checkLet : (top : Bool) -> -- top level, unbound implicits bound here
             ImplicitMode ->
             annot -> Env Term vars ->
             Name -> 
             (ty : RawImp annot) -> 
             (val : RawImp annot) -> 
             (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot [Ctxt ::: Defs, UST ::: UState annot, EST ::: EState vars]
                  (Term vars, Term vars) 
  checkLet top impmode loc env n ty val scope expected
      = do (tyv, tyt) <- check top impmode env ty (Just TType)
           (valv, valt) <- check top impmode env val (Just tyv)
           let env' : Env Term (n :: _) = Let valv tyv :: env
           weakenEState
           (scopev, scopet) <- check top impmode env' scope (map weaken expected)
           strengthenEState top loc
           checkExp loc env (Bind n (Let valv tyv) scopev)
                            (Bind n (Let valv tyv) scopet)
                            expected

-- Find any holes in the resulting expression, and implicitly bind them
-- at the top level (i.e. they can't depend on any explicitly given
-- arguments).
-- Return the updated term and type, and the names of holes which occur
findHoles : ImplicitMode -> Env Term vars -> Term vars -> Term vars ->
            Core annot [Ctxt ::: Defs, UST ::: UState annot]
                 (Term vars, Term vars, List Name) 
findHoles NONE env tm exp = pure (tm, exp, [])
findHoles (PI False) env tm exp = pure (tm, exp, [])
findHoles mode env tm exp
    = do new HVar []
         tm <- holes tm
         hs <- get HVar
         delete HVar
         gam <- getCtxt
         let (tm, ty) = bindTopImplicits mode gam env (reverse hs) tm exp
         pure (tm, ty, map fst hs)
  where
    data HVar : Type where -- empty type to label the local state

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
                  Just (Hole _, ty) =>
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
                                      
renameImplicits : Term vars -> Term vars
renameImplicits (Bind (PV n) b sc) 
    = Bind (UN n) b (renameImplicits (renameTop (UN n) sc))
renameImplicits (Bind n b sc) 
    = Bind n b (renameImplicits sc)
renameImplicits t = t

elabTerm : Env Term vars ->
           ImplicitMode ->
           (term : RawImp annot) ->
           (tyin : Maybe (Term vars)) ->
           Core annot [Ctxt ::: Defs, UST ::: UState annot]
                 (Term vars, Term vars) 
elabTerm env impmode tm tyin
    = do resetHoles
         new EST initEState
         (chktm, ty) <- call $ check True impmode env tm tyin
         solveConstraints
         est <- get EST
         -- Bind the implicits and any unsolved holes they refer to
         -- This is in implicit mode 'PATTERN' and 'PI'
         let fullImps = reverse $ toBind est
         clearToBind -- remove the bound holes
         delete EST
         gam <- getCtxt
         let (restm, resty) = bindImplicits impmode gam env
                                            (dropTmIn fullImps) chktm ty
         traverse (\n => implicitBind n) (map fst fullImps)
         gam <- getCtxt
         (ptm, pty, bound) <- findHoles impmode env (normaliseHoles gam env restm) resty
         -- Give implicit bindings their proper names, as UNs not PVs
         let ptm' = renameImplicits ptm
         let pty' = renameImplicits pty
         -- Drop any holes we created which aren't used in the resulting
         -- term
         traverse (\n => implicitBind n) bound
--          putStrLn "--- CONSTRAINTS AND HOLES ---"
--          dumpConstraints 
         pure (ptm', pty')

export
inferTerm : Env Term vars ->
            ImplicitMode ->
            (term : RawImp annot) ->
            Core annot [Ctxt ::: Defs, UST ::: UState annot]
                 (Term vars, Term vars) 
inferTerm env impmode tm = elabTerm env impmode tm Nothing

export
checkTerm : Env Term vars ->
            ImplicitMode ->
            (term : RawImp annot) -> (ty : Term vars) ->
            Core annot [Ctxt ::: Defs, UST ::: UState annot]
                 (Term vars) 
checkTerm env impmode tm ty 
    = do (tm_elab, _) <- elabTerm env impmode tm (Just ty)
         pure tm_elab

