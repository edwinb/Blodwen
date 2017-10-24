module TTImp.Elab

import TTImp.TTImp
import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT
import Core.Typecheck
import Core.Unify

import Data.List
import Data.List.Views

%default covering

-- How the elaborator should deal with IBindVar:
-- * NONE: IBindVar is not valid (rhs of an definition, top level expression)
-- * PI True: Bind implicits as Pi, in the appropriate scope, and bind
--            any additional holes
-- * PI False: As above, but don't bind additional holes
-- * PATTERN: Bind implicits as PVar, but only at the top level
public export
data ImplicitMode = NONE | PI Bool | PATTERN

public export
data ElabMode = InType | InLHS | InExpr

record ElabState (vars : List Name) where
  constructor MkElabState
  boundNames : List (Name, (Term vars, Term vars))
                  -- implicit pattern/type variable bindings and the 
                  -- term/type they elaborated to
  toBind : List (Name, (Term vars, Term vars))
                  -- implicit pattern/type variables which haven't been
                  -- bound yet.
  defining : Name -- Name of thing we're currently defining

public export
Elaborator : Type -> Type
Elaborator annot
    = {vars : List Name} ->
      Ref Ctxt Defs -> Ref UST (UState annot) ->
      Ref ImpST (ImpState annot) ->
      Env Term vars -> NestedNames vars -> 
      ImpDecl annot -> Core annot ()


-- A label for the internal elaborator state
data EST : Type where

initEState : Name -> ElabState vars
initEState n = MkElabState [] [] n

EState : List Name -> Type
EState = ElabState

-- weaken the unbound implicits which have not yet been bound
-- weakenEState : CoreM annot [EST ::: EState vs] [EST ::: EState (n :: vs)] ()
-- weakenEState 
--     = do est <- get EST
--          putM EST (MkElabState (map wknTms (boundNames est))
--                                (map wknTms (toBind est)))
--   where
--     wknTms : (Name, (Term vs, Term vs)) -> 
--              (Name, (Term (n :: vs), Term (n :: vs)))
--     wknTms (f, (x, y)) = (f, (weaken x, weaken y))

weakenedEState : {auto e : Ref EST (EState vs)} ->
                 Core annot (Ref EST (EState (n :: vs)))
weakenedEState
    = do est <- get EST
         e' <- newRef EST (MkElabState (map wknTms (boundNames est))
                                       (map wknTms (toBind est))
                                       (defining est))
         pure e'
  where
    wknTms : (Name, (Term vs, Term vs)) -> 
             (Name, (Term (n :: vs), Term (n :: vs)))
    wknTms (f, (x, y)) = (f, (weaken x, weaken y))

-- remove the outermost variable from the unbound implicits which have not
-- yet been bound. If it turns out to depend on it, that means it can't
-- be bound at the top level, which is an error.
strengthenedEState : {auto e : Ref EST (EState (n :: vs))} ->
                     (top : Bool) -> annot ->
                     Core annot (EState vs)
strengthenedEState True loc = do est <- get EST
                                 pure (initEState (defining est))
strengthenedEState False loc 
    = do est <- get EST
         bns <- traverse strTms (boundNames est)
         todo <- traverse strTms (toBind est)
         pure (MkElabState bns todo (defining est))
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
             Core annot (Name, (Term vs, Term vs))
    strTms {vs} (f, (x, y))
        = case (removeArg x, shrinkTerm y (DropCons SubRefl)) of
               (Just x', Just y') => pure (f, (x', y'))
               _ => throw (GenericMsg loc ("Invalid unbound implicit " ++ show f))

clearEState : {auto e : Ref EST (EState vs)} ->
              Core annot ()
clearEState = do est <- get EST
                 put EST (initEState (defining est))

clearToBind : {auto e : Ref EST (EState vs)} ->
              Core annot ()
clearToBind
    = do est <- get EST
--          putStrLn $ "Clearing holes: " ++ show (map fst (toBind est))
         put EST (record { toBind = [] } est)
   
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

convert : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
          {auto e : Ref EST (EState vars)} ->
          annot -> ElabMode -> Env Term vars -> NF vars -> NF vars -> 
          Core annot (List Name)
convert loc elabmode env x y 
    = let umode = case elabmode of
                       InLHS => InLHS
                       _ => InTerm in
          catch (do solveConstraints umode
                    log 10 $ "Unifying " ++ show (quote empty env x) ++ " and " 
                                         ++ show (quote empty env y)
                    vs <- unify umode loc env x y
                    solveConstraints umode
                    pure vs)
            (\err => do gam <- getCtxt 
                        throw (WhenUnifying loc (normaliseHoles gam env (quote empty env x))
                                                (normaliseHoles gam env (quote empty env y))
                                  err))
  
-- Get the implicit arguments that need to be inserted at this point
-- in a function application. Do this by reading off implicit Pis
-- in the expected type ('ty') and adding new holes for each.
-- Return the (normalised) remainder of the type, and the list of
-- implicits added
getImps : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
          {auto e : Ref EST (EState vars)} ->
          annot -> Env Term vars ->
          (ty : NF vars) -> List (Term vars) ->
          Core annot (NF vars, List (Term vars)) 
getImps loc env (NBind bn (Pi Implicit ty) sc) imps
    = do hn <- genName (nameRoot bn)
         addNamedHole hn env (quote empty env ty)
         let arg = mkConstantApp hn env
         getImps loc env (sc (toClosure True env arg)) (arg :: imps)
getImps loc env ty imps = pure (ty, reverse imps)

--- When converting, add implicits until we've applied enough for the
--- expected type
convertImps : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
              {auto e : Ref EST (EState vars)} ->
              annot -> Env Term vars ->
              (got : NF vars) -> (exp : NF vars) -> List (Term vars) ->
              Core annot (NF vars, List (Term vars))
convertImps loc env (NBind bn (Pi Implicit ty) sc) (NBind bn' (Pi Implicit ty') sc') imps
    = pure (NBind bn (Pi Implicit ty) sc, reverse imps)
convertImps loc env (NBind bn (Pi Implicit ty) sc) exp imps
    = do hn <- genName (nameRoot bn)
         addNamedHole hn env (quote empty env ty)
         let arg = mkConstantApp hn env
         convertImps loc env (sc (toClosure False env arg)) exp (arg :: imps)
convertImps loc env got exp imps = pure (got, reverse imps)

checkExp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
           {auto e : Ref EST (EState vars)} ->
           annot -> ElabMode -> Env Term vars ->
           (term : Term vars) -> (got : Term vars) -> 
           (exp : Maybe (Term vars)) ->
           Core annot (Term vars, Term vars) 
checkExp loc elabmode env tm got Nothing
    = pure (tm, got)
checkExp loc elabmode env tm got (Just exp) 
    = do gam <- getCtxt
         let expnf = nf gam env exp
         (got', imps) <- convertImps loc env (nf gam env got) expnf []
         constr <- convert loc elabmode env got' expnf
         case constr of
              [] => pure (apply tm imps, quote empty env got')
              cs => do gam <- getCtxt
                       c <- addConstant env (apply tm imps) exp cs
                       pure (mkConstantApp c env, got)

inventFnType : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
               {auto e : Ref EST (EState vars)} ->
               Env Term vars ->
               (bname : Name) ->
               Core annot (Term vars, Term (bname :: vars))
inventFnType env bname
    = do an <- genName "argh"
         scn <- genName "sch"
         argTy <- addBoundName an env TType
         scTy <- addBoundName scn (Pi Explicit argTy :: env) TType
         pure (argTy, scTy)

mutual
  check : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
          {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
          Elaborator annot ->
          (top : Bool) -> -- top level, unbound implicits bound here
          ImplicitMode -> ElabMode ->
          Env Term vars -> NestedNames vars ->
          (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
          Core annot (Term vars, Term vars) 
  check process top impmode InLHS env nest tm exp -- don't expand implicit lambda on LHS
      = checkImp process top impmode InLHS env nest tm exp
  check process top impmode elabmode env nest tm exp 
      = let tm' = insertImpLam env tm exp in
            checkImp process top impmode elabmode env nest tm' exp

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

  checkImp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             (top : Bool) -> -- top level, unbound implicits bound here
             ImplicitMode -> ElabMode ->
             Env Term vars -> NestedNames vars ->
             (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
             Core annot (Term vars, Term vars) 
  checkImp process top impmode elabmode env nest (IVar loc x) expected 
      = case lookup x (names nest) of
             Just (n', tm) =>
                  do gam <- getCtxt
                     case lookupTy n' gam of
                          Nothing => throw (UndefinedName loc n')
                          Just ty => 
                             let tyenv = useVars (getArgs tm) (embed ty) in
                                do log 5 $ "Type of " ++ show n' ++ " : " ++ show tyenv
                                   checkExp loc elabmode env tm tyenv expected
             _ => do (x', varty) <- infer loc env (RVar x)
                     gam <- getCtxt
                     -- If the variable has an implicit binder in its type, add
                     -- the implicits here
                     (ty, imps) <- getImps loc env (nf gam env varty) []
                     checkExp loc elabmode env (apply x' imps) (quote empty env ty) expected
    where
      useVars : List (Term vars) -> Term vars -> Term vars
      useVars [] sc = sc
      useVars (a :: as) (Bind n (Pi _ ty) sc) 
           = Bind n (Let a ty) (useVars (map weaken as) sc)
      useVars _ sc = sc -- Can't happen?

  checkImp process top impmode elabmode env nest (IPi loc plicity Nothing ty retTy) expected 
      = do n <- genName "pi"
           checkPi process top impmode elabmode loc env nest plicity n ty retTy expected
  checkImp process top impmode elabmode env nest (IPi loc plicity (Just n) ty retTy) expected 
      = checkPi process top impmode elabmode loc env nest plicity n ty retTy expected
  checkImp process top impmode elabmode env nest (ILam loc plicity n ty scope) expected
      = checkLam process top impmode elabmode loc env nest plicity n ty scope expected
  checkImp process top impmode elabmode env nest (ILet loc n nTy nVal scope) expected 
      = checkLet process top impmode elabmode loc env nest n nTy nVal scope expected
  checkImp {vars} {c} {u} {i} process top impmode elabmode env nest (ILocal loc nested scope) expected 
      = do let defNames = definedInBlock nested
           est <- get EST
           let f = defining est
           let nest' = record { names $= ((map (applyEnv f) defNames) ++) } nest
           traverse (process c u i env nest') (map (updateName nest') nested)
           checkImp process top impmode elabmode env nest' scope expected
    where
      applyEnv : Name -> Name -> (Name, (Name, Term vars))
      applyEnv outer inner = (inner, (GN (Nested outer inner), 
                                      mkConstantApp (GN (Nested outer inner)) env))
      
      -- Update the names in the declarations to the new 'nested' names.
      -- When we encounter the names in elaboration, we'll update to an
      -- application of the nested name.
      newName : NestedNames vars -> Name -> Name
      newName nest n 
          = case lookup n (names nest) of
                 Just (n', _) => n'
                 _ => n

      updateTyName : NestedNames vars -> ImpTy annot -> ImpTy annot
      updateTyName nest (MkImpTy loc n ty) = MkImpTy loc (newName nest n) ty

      updateDataName : NestedNames vars -> ImpData annot -> ImpData annot
      updateDataName nest (MkImpData loc n tycons dcons)
          = MkImpData loc (newName nest n) tycons (map (updateTyName nest) dcons)

      updateName : NestedNames vars -> ImpDecl annot -> ImpDecl annot
      updateName nest (IClaim loc ty) = IClaim loc (updateTyName nest ty)
      updateName nest (IDef loc n cs) = IDef loc (newName nest n) cs
      updateName nest (IData loc d) = IData loc (updateDataName nest d)
      updateName nest i = i

  checkImp process top impmode elabmode env nest (IApp loc fn arg) expected 
      = do (fntm, fnty) <- check process top impmode elabmode env nest fn Nothing
           gam <- getCtxt
           -- If the function has an implicit binder in its type, add
           -- the implicits here
           (scopeTy, impArgs) <- getImps loc env (nf gam env fnty) []
           gam <- getCtxt
           case scopeTy of
                NBind _ (Pi _ ty) scdone =>
                  do (argtm, argty) <- check process top impmode elabmode env nest arg (Just (quote empty env ty))
                     let sc' = scdone (toClosure False env argtm)
                     gam <- getCtxt
                     checkExp loc elabmode env (App (apply fntm impArgs) argtm)
                                  (quote gam env sc') expected
                _ => 
                  do bn <- genName "aTy"
                     -- invent names for the argument and return types
                     (expty, scty) <- inventFnType env bn
                     -- Check the argument type against the invented arg type
                     (argtm, argty) <- 
                         check process top impmode elabmode env nest arg (Just expty) -- (Bind bn (Pi Explicit expty) scty))
                     -- Check the type of 'fn' is an actual function type
                     gam <- getCtxt
                     (fnchk, _) <-
                         checkExp loc elabmode env fntm 
                                  (Bind bn (Pi Explicit expty) scty) 
                                  (Just (quote gam env scopeTy))
                     checkExp loc elabmode env (App fnchk argtm)
                                  (Bind bn (Let argtm argty) scty) expected
  checkImp process top impmode elabmode env nest (IPrimVal loc x) expected 
      = do (x', ty) <- infer loc env (RPrimVal x)
           checkExp loc elabmode env x' ty expected
  checkImp process top impmode elabmode env nest (IType loc) exp
      = checkExp loc elabmode env TType TType exp
  checkImp process top impmode InExpr env nest (IBindVar loc str) exp
      = throw (BadImplicit loc str)
  checkImp process top impmode elabmode env nest (IBindVar loc str) Nothing
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
  checkImp process top impmode elabmode env nest (IBindVar loc str) (Just expected) 
      = do let n = PV str
           est <- get EST
           case lookup n (boundNames est) of
                Nothing =>
                  do tm <- addBoundName n env expected
                     log 5 $ "Added Bound implicit " ++ show (n, (tm, expected))
                     gam <- getCtxt
                     put EST 
                         (record { boundNames $= ((n, (tm, expected)) ::),
                                   toBind $= ((n, (tm, expected)) :: ) } est)
                     pure (tm, expected)
                Just (tm, ty) =>
                     checkExp loc elabmode env tm ty (Just expected)
  checkImp process top impmode elabmode env nest (Implicit loc) Nothing
      = do t <- addHole env TType
           let hty = mkConstantApp t env
           n <- addHole env hty
           pure (mkConstantApp n env, hty)
  checkImp process top impmode elabmode env nest (Implicit loc) (Just expected) 
      = do n <- addHole env expected
           pure (mkConstantApp n env, expected)
 
  checkPi : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot ->
            (top : Bool) -> -- top level, unbound implicits bound here
            ImplicitMode -> ElabMode ->
            annot -> Env Term vars -> NestedNames vars -> PiInfo -> Name -> 
            (argty : RawImp annot) -> (retty : RawImp annot) ->
            Maybe (Term vars) ->
            Core annot (Term vars, Term vars) 
  checkPi process top impmode elabmode loc env nest info n argty retty expected
      = do (tyv, tyt) <- check process False impmode elabmode env nest argty (Just TType)
           let env' : Env Term (n :: _) = Pi info tyv :: env
           est <- get EST
           let argImps = if top then (reverse $ toBind est) else []
           when top $ clearToBind 
           e' <- weakenedEState 
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} process top impmode elabmode env' (weaken nest') retty (Just TType)
           est <- get {ref=e'} EST
           let scopeImps = reverse $ toBind est
           st' <- strengthenedEState {e=e'} top loc
           put EST st'
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
                      checkExp loc elabmode env binder bindert expected
                _ => checkExp loc elabmode env (Bind n (Pi info tyv) scopev)
                                      TType expected

  checkLam : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             (top : Bool) -> -- top level, unbound implicits bound here
             ImplicitMode -> ElabMode ->
             annot -> Env Term vars -> NestedNames vars -> PiInfo -> Name ->
             (ty : RawImp annot) -> (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkLam process top impmode elabmode loc env nest plicity n ty scope (Just (Bind bn (Pi Explicit pty) psc))
      = do (tyv, tyt) <- check process top impmode elabmode env nest ty (Just TType)
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check process {e=e'} top impmode elabmode (Pi plicity pty :: env) 
                                     (weaken nest') scope 
                                     (Just (renameTop n psc))
           st' <- strengthenedEState top loc
           put EST st'
           checkExp loc elabmode env (Bind n (Lam plicity tyv) scopev)
                        (Bind n (Pi plicity tyv) scopet)
                        (Just (Bind bn (Pi plicity pty) psc))
  checkLam process top impmode elabmode loc env nest plicity n ty scope expected
      = do (tyv, tyt) <- check process top impmode elabmode env nest ty (Just TType)
           let env' : Env Term (n :: _) = Pi Explicit tyv :: env
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} process top impmode elabmode env' (weaken nest') scope Nothing
           st' <- strengthenedEState top loc
           put EST st'
           checkExp loc elabmode env (Bind n (Lam plicity tyv) scopev)
                        (Bind n (Pi plicity tyv) scopet)
                        expected
  
  checkLet : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             (top : Bool) -> -- top level, unbound implicits bound here
             ImplicitMode -> ElabMode ->
             annot -> Env Term vars -> NestedNames vars ->
             Name -> 
             (ty : RawImp annot) -> 
             (val : RawImp annot) -> 
             (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkLet process top impmode elabmode loc env nest n ty val scope expected
      = do (tyv, tyt) <- check process top impmode elabmode env nest ty (Just TType)
           (valv, valt) <- check process top impmode elabmode env nest val (Just tyv)
           let env' : Env Term (n :: _) = Let valv tyv :: env
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} process top impmode elabmode env' 
                                     (weaken nest') scope (map weaken expected)
           st' <- strengthenedEState top loc
           put EST st'
           checkExp loc elabmode env (Bind n (Let valv tyv) scopev)
                                     (Bind n (Let valv tyv) scopet)
                                     expected

-- Find any holes in the resulting expression, and implicitly bind them
-- at the top level (i.e. they can't depend on any explicitly given
-- arguments).
-- Return the updated term and type, and the names of holes which occur
findHoles : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            ImplicitMode -> Env Term vars -> Term vars -> Term vars ->
            Core annot (Term vars, Term vars, List Name) 
findHoles NONE env tm exp = pure (tm, exp, [])
findHoles (PI False) env tm exp = pure (tm, exp, [])
findHoles mode env tm exp
    = do h <- newRef HVar []
         tm <- holes h tm
         hs <- get HVar
         gam <- getCtxt
         log 5 $ "Extra implicits to bind: " ++ show (reverse hs)
         let (tm', ty) = bindTopImplicits mode gam env (reverse hs) tm exp
         pure (tm', ty, map fst hs)
  where
    data HVar : Type where -- empty type to label the local state

    mkType : (vars : List Name) -> Term hs -> Maybe (Term hs)
    mkType (v :: vs) (Bind tm (Pi _ ty) sc) 
        = do sc' <- mkType vs sc
             shrinkTerm sc' (DropCons SubRefl)
    mkType _ tm = pure tm

    processHole : Ref HVar (List (Name, ClosedTerm)) ->
                  Name -> (vars : List Name) -> ClosedTerm ->
                  Core annot ()
    processHole h n vars ty
       = do hs <- get HVar
--             putStrLn $ "IMPLICIT: " ++ show (n, vars, ty)
            case mkType vars ty of
                 Nothing => pure ()
                 Just impTy =>
                    case lookup n hs of
                         Just _ => pure ()
                         Nothing => put HVar ((n, impTy) :: hs)

    holes : Ref HVar (List (Name, ClosedTerm)) ->
            Term vars -> 
            Core annot (Term vars)
    holes h {vars} (Ref nt fn) 
        = do gam <- getCtxt
             case lookupDefTy fn gam of
                  Just (Hole _, ty) =>
                       do processHole h fn vars ty
                          pure (Ref nt fn)
                  _ => pure (Ref nt fn)
    holes h (App fn arg)
        = do fn' <- holes h fn
             arg' <- holes h arg
             pure (App fn' arg')
    -- Allow implicits under 'Pi' and 'PVar' only
    holes h (Bind y (Pi imp ty) sc)
        = do ty' <- holes h ty
             sc' <- holes h sc
             pure (Bind y (Pi imp ty') sc')
    holes h (Bind y (PVar ty) sc)
        = do ty' <- holes h ty
             sc' <- holes h sc
             pure (Bind y (PVar ty') sc')
    holes h tm = pure tm

renameImplicits : Gamma -> Term vars -> Term vars
renameImplicits gam (Bind (PV n) b sc) 
    = case lookupDef (PV n) gam of
           Just (PMDef _ _ def) =>
--                 trace ("OOPS " ++ show n ++ " = " ++ show def) $
                    Bind (UN n) b (renameImplicits gam (renameTop (UN n) sc))
           _ => Bind (UN n) b (renameImplicits gam (renameTop (UN n) sc))
renameImplicits gam (Bind n b sc) 
    = Bind n b (renameImplicits gam sc)
renameImplicits gam t = t

elabTerm : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST (UState annot)} ->
           {auto i : Ref ImpST (ImpState annot)} ->
           Elaborator annot ->
           Name ->
           Env Term vars -> NestedNames vars ->
           ImplicitMode -> ElabMode ->
           (term : RawImp annot) ->
           (tyin : Maybe (Term vars)) ->
           Core annot (Term vars, Term vars) 
elabTerm process defining env nest impmode elabmode tm tyin
    = do resetHoles
         e <- newRef EST (initEState defining)
         (chktm, ty) <- Elab.check {e} process True impmode elabmode env nest tm tyin
         solveConstraints (case elabmode of
                                InLHS => InLHS
                                _ => InTerm)
         est <- get EST
         -- Bind the implicits and any unsolved holes they refer to
         -- This is in implicit mode 'PATTERN' and 'PI'
         let fullImps = reverse $ toBind est
         clearToBind -- remove the bound holes
         gam <- getCtxt
         log 5 $ "Binding implicits " ++ show (dropTmIn fullImps) ++
                 " in " ++ show chktm
         let (restm, resty) = bindImplicits impmode gam env
                                            (dropTmIn fullImps) chktm ty
         traverse (\n => implicitBind n) (map fst fullImps)
         gam <- getCtxt
         (ptm, pty, bound) <- findHoles impmode env (normaliseHoles gam env restm) resty
         -- Give implicit bindings their proper names, as UNs not PVs
         gam <- getCtxt
         let ptm' = renameImplicits gam ptm
         let pty' = renameImplicits gam pty
         -- Drop any holes we created which aren't used in the resulting
         -- term
         traverse (\n => implicitBind n) bound
         dumpConstraints 
         pure (ptm', pty')

export
inferTerm : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST (UState annot)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot -> 
            Name ->
            Env Term vars -> NestedNames vars ->
            ImplicitMode -> ElabMode ->
            (term : RawImp annot) ->
            Core annot (Term vars, Term vars) 
inferTerm process defining env nest impmode elabmode tm 
    = elabTerm process defining env nest impmode elabmode tm Nothing

export
checkTerm : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST (UState annot)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot ->
            Name ->
            Env Term vars -> NestedNames vars ->
            ImplicitMode -> ElabMode ->
            (term : RawImp annot) -> (ty : Term vars) ->
            Core annot (Term vars) 
checkTerm process defining env nest impmode elabmode tm ty 
    = do (tm_elab, _) <- elabTerm process defining env nest impmode elabmode tm (Just ty)
         pure tm_elab

