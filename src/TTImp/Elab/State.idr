module TTImp.Elab.State

import TTImp.TTImp
import Core.CaseTree
import Core.Context
import Core.TT
import Core.Normalise
import Core.Unify

import Data.List
import Data.CSet

-- How the elaborator should deal with IBindVar:
-- * NONE: IBindVar is not valid (rhs of an definition, top level expression)
-- * PI rig: Bind implicits as Pi, in the appropriate scope, and bind
--           any additional holes, with given multiplicity
public export
data ImplicitMode = NONE | PI RigCount | PATTERN

public export
data ElabMode = InType | InLHS | InExpr

export
Eq ElabMode where
  InType == InType = True
  InLHS == InLHS = True
  InExpr == InExpr = True
  _ == _ = False

data BoundVar : List Name -> Type where
  MkBoundVar : Term outer -> Term outer -> BoundVar (vars ++ outer)

public export
record EState (vars : List Name) where
  constructor MkElabState
  -- The outer environment in which we're running the elaborator. Things here should
  -- be considered parametric as far as case expression elaboration goes, and are
  -- the only things that unbound implicits can depend on
  outerEnv : Env Term outer
  subEnv : SubVars outer vars
  boundNames : List (Name, (Term vars, Term vars))
                  -- implicit pattern/type variable bindings and the 
                  -- term/type they elaborated to
  toBind : List (Name, (Term vars, Term vars))
                  -- implicit pattern/type variables which haven't been
                  -- bound yet.
  lhsPatVars : List String
                  -- names which we've bound in elab mode InLHS (i.e. not
                  -- in a dot pattern). We keep track of this because every
                  -- occurrence other than the first needs to be dotted
  allPatVars : List Name -- All pattern variables, which need to be cleared after elaboration
  asVariables : List (Name, RigCount) -- Names bound in @-patterns
  implicitsUsed : List (Maybe Name)
                            -- explicitly given implicits which have been used
                            -- in the current application (need to keep track, as
                            -- they may not be given in the same order as they are 
                            -- needed in the type)
  linearUsed : List (x ** Elem x vars) -- Rig1 bound variables used in the term so far
  holesMade : List Name -- Explicit hole names used in the term so far
  defining : Name -- Name of thing we're currently defining

public export
Elaborator : Type -> Type
Elaborator annot
    = {vars : List Name} ->
      Ref Ctxt Defs -> Ref UST (UState annot) ->
      Ref ImpST (ImpState annot) ->
      Env Term vars -> NestedNames vars -> 
      ImpDecl annot -> Core annot ()

public export
record ElabInfo annot where
  constructor MkElabInfo
  topLevel : Bool -- at the top level of a type sig (i.e not in a higher order type)
  implicitMode : ImplicitMode
  elabMode : ElabMode
  implicitsGiven : List (Maybe Name, RawImp annot)
  lamImplicits : List (Maybe Name, RawImp annot)
  dotted : Bool -- are we under a dot pattern? (IMustUnify)

export
initElabInfo : ImplicitMode -> ElabMode -> ElabInfo annot
initElabInfo imp elab = MkElabInfo True imp elab [] [] False

-- A label for the internal elaborator state
export
data EST : Type where

export
initEStateSub : Name -> Env Term outer -> SubVars outer vars -> EState vars
initEStateSub n env sub = MkElabState env sub [] [] [] [] [] [] [] [] n

export
initEState : Name -> Env Term vars -> EState vars
initEState n env = initEStateSub n env SubRefl

export
updateEnv : Env Term new -> SubVars new vars -> EState vars -> EState vars
updateEnv env sub st
    = MkElabState env sub
                  (boundNames st) (toBind st)
                  (lhsPatVars st) (allPatVars st) (asVariables st)
                  (implicitsUsed st) (linearUsed st)
                  (holesMade st) (defining st)

-- Convenient way to record all of the elaborator state, for the times
-- we need to backtrack
export
AllState : List Name -> Type -> Type
AllState vars annot = (Defs, UState annot, EState vars, ImpState annot)

export
getAllState : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
              {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
              Core annot (AllState vars annot)
getAllState
    = do ctxt <- get Ctxt
         ust <- get UST
         est <- get EST
         ist <- get ImpST
         pure (ctxt, ust, est, ist)

export
putAllState : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
           {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
           AllState vars annot -> Core annot ()
putAllState (ctxt, ust, est, ist)
    = do put Ctxt ctxt
         put UST ust
         put EST est
         put ImpST ist

export
getState : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
           {auto i : Ref ImpST (ImpState annot)} ->
           Core annot (Defs, UState annot, ImpState annot)
getState
    = do ctxt <- get Ctxt
         ust <- get UST
         ist <- get ImpST
         pure (ctxt, ust, ist)

export
putState : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
           {auto i : Ref ImpST (ImpState annot)} ->
           (Defs, UState annot, ImpState annot)-> Core annot ()
putState (ctxt, ust, ist)
    = do put Ctxt ctxt
         put UST ust
         put ImpST ist

export
inTmpState : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Core annot a -> Core annot a
inTmpState p
    = do st <- getState
         p' <- p
         putState st
         pure p'

export
saveImps : {auto e : Ref EST (EState vars)} -> Core annot (List (Maybe Name))
saveImps
    = do est <- get EST
         put EST (record { implicitsUsed = [] } est)
         pure (implicitsUsed est)

export
restoreImps : {auto e : Ref EST (EState vars)} -> List (Maybe Name) -> Core annot ()
restoreImps imps
    = do est <- get EST
         put EST (record { implicitsUsed = imps } est)

export
usedImp : {auto e : Ref EST (EState vars)} -> Maybe Name -> Core annot ()
usedImp imp
    = do est <- get EST
         put EST (record { implicitsUsed $= (imp :: ) } est)

-- Check that explicitly given implicits that we've used are allowed in the
-- the current application
export
checkUsedImplicits : {auto e : Ref EST (EState vars)} ->
                     annot -> Env Term vars -> ElabMode ->
                     List (Maybe Name) -> 
                     List (Maybe Name, RawImp annot) -> Term vars -> Core annot ()
checkUsedImplicits loc env mode used [] tm = pure ()
checkUsedImplicits loc env mode used given tm
    = let unused = filter (notUsed mode) given in
          case unused of
               [] => -- remove the things which were given, and are now part of
                     -- an application, from the 'implicitsUsed' list, because
                     -- we've now verified that they were used correctly.
                     restoreImps (filter (\x => not (x `elem` map fst given)) used)
               ((Just n, _) :: _) => throw (InvalidImplicit loc env n tm)
               ((Nothing, _) :: _) => throw (GenericMsg loc "No auto implicit here")
  where
    notUsed : ElabMode -> (Maybe Name, RawImp annot) -> Bool
    notUsed InLHS (n, IAs _ _ (Implicit _)) = False -- added by elaborator, ignore it
    notUsed _ (x, _) = not (x `elem` used)

export
weakenedEState : {auto e : Ref EST (EState vs)} ->
                 Core annot (Ref EST (EState (n :: vs)))
weakenedEState
    = do est <- get EST
         e' <- newRef EST (MkElabState (outerEnv est)
                                       (DropCons (subEnv est))
                                       (map wknTms (boundNames est))
                                       (map wknTms (toBind est))
                                       (lhsPatVars est)
                                       (allPatVars est)
                                       (asVariables est)
                                       (implicitsUsed est)
                                       (map wknLoc (linearUsed est))
                                       (holesMade est)
                                       (defining est))
         pure e'
  where
    wknLoc : (x ** Elem x vs) -> (x ** Elem x (n :: vs))
    wknLoc (_ ** p) = (_ ** There p)

    wknTms : (Name, (Term vs, Term vs)) -> 
             (Name, (Term (n :: vs), Term (n :: vs)))
    wknTms (f, (x, y)) = (f, (weaken x, weaken y))

-- remove the outermost variable from the unbound implicits which have not
-- yet been bound. If it turns out to depend on it, that means it can't
-- be bound at the top level, which is an error.
export
strengthenedEState : {auto e : Ref EST (EState (n :: vs))} ->
                     {auto c : Ref Ctxt Defs} ->
                     (top : Bool) -> annot -> Env Term (n :: vs) ->
                     Core annot (EState vs)
-- strengthenedEState True loc env 
--     = do est <- get EST
--          pure (initEState (defining est))
strengthenedEState {n} {vs} _ loc env
    = do est <- get EST
         defs <- get Ctxt
         bns <- traverse (strTms defs) (boundNames est)
         todo <- traverse (strTms defs) (toBind est)
         let lvs = mapMaybe dropTop (linearUsed est)
         svs <- dropSub (subEnv est)
         pure (MkElabState (outerEnv est)
                           svs
                           bns todo (lhsPatVars est)
                                    (allPatVars est)
                                    (asVariables est)
                                    (implicitsUsed est) 
                                    lvs
                                    (holesMade est)
                                    (defining est))
  where
    dropSub : SubVars xs (y :: ys) -> Core annot (SubVars xs ys)
    dropSub (DropCons sub) = pure sub
    dropSub _ = throw (InternalError "Badly formed weakened environment")

    -- Remove any instance of the top level local variable from an
    -- application. Fail if it turns out to be necessary.
    -- NOTE: While this isn't strictly correct given the type of the hole
    -- which stands for the unbound implicits, it's harmless because we
    -- never actualy *use* that hole - this process is only to ensure that the
    -- unbound implicit doesn't depend on any variables it doesn't have
    -- in scope.
    removeArgVars : List (Term (n :: vs)) -> Maybe (List (Term vs))
    removeArgVars [] = pure []
    removeArgVars (Local r (There p) :: args) 
        = do args' <- removeArgVars args
             pure (Local r p :: args')
    removeArgVars (Local r Here :: args) 
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

    strTms : Defs -> (Name, (Term (n :: vs), Term (n :: vs))) -> 
             Core annot (Name, (Term vs, Term vs))
    strTms defs (f, (x, y))
        = let xnf = normaliseHoles defs env x
              ynf = normaliseHoles defs env y in
              case (removeArg xnf, shrinkTerm ynf (DropCons SubRefl)) of
               (Just x', Just y') => pure (f, (x', y'))
               _ => throw (GenericMsg loc ("Invalid unbound implicit " ++ 
                               show f ++ " " ++ show xnf ++ " : " ++ show ynf))

    dropTop : (x ** Elem x (n :: vs)) -> Maybe (x ** Elem x vs)
    dropTop (_ ** Here) = Nothing
    dropTop (_ ** There p) = Just (_ ** p)

elemEmbedSub : SubVars small vars -> Elem x small -> Elem x vars
elemEmbedSub SubRefl y = y
elemEmbedSub (DropCons prf) y = There (elemEmbedSub prf y)
elemEmbedSub (KeepCons prf) Here = Here
elemEmbedSub (KeepCons prf) (There later) = There (elemEmbedSub prf later)

embedSub : SubVars small vars -> Term small -> Term vars
embedSub sub (Local r prf) = Local r (elemEmbedSub sub prf)
embedSub sub (Ref x fn) = Ref x fn
embedSub sub (Bind x b tm) 
    = Bind x (assert_total (map (embedSub sub) b))
             (embedSub (KeepCons sub) tm)
embedSub sub (App f a) = App (embedSub sub f) (embedSub sub a)
embedSub sub (PrimVal x) = PrimVal x
embedSub sub Erased = Erased
embedSub sub TType = TType

-- Make a hole for a bound implicit in the outer environment
export
mkOuterHole : {auto e : Ref EST (EState vars)} ->
              {auto c : Ref Ctxt Defs} ->
              {auto e : Ref UST (UState annot)} ->
              annot -> Name -> Bool -> Maybe (Term vars) ->
              Core annot (Term vars, Term vars)
mkOuterHole {vars} loc n patvar (Just expected)
    = do est <- get EST
         let sub = subEnv est
         case shrinkTerm expected sub of
              Nothing => 
                  throw (GenericMsg loc ("Can't make hole for " ++ show n ++ " here "
                            ++ show expected ++ " " ++ show vars))
              Just exp' => 
                  do tm <- addBoundName loc n patvar (outerEnv est) exp'
                     pure (embedSub sub tm, embedSub sub exp')
mkOuterHole loc n patvar Nothing
    = do est <- get EST
         let sub = subEnv est
         let env = outerEnv est
         t <- addHole loc env TType
         let ty = mkConstantApp t env
         tm <- addBoundName loc n patvar env ty
         pure (embedSub sub tm, embedSub sub ty)

export
clearToBind : {auto e : Ref EST (EState vs)} ->
              Core annot ()
clearToBind
    = do est <- get EST
         put EST (record { toBind = [] } est)

export
clearPatVars : {auto e : Ref EST (EState vs)} ->
               {auto c : Ref Ctxt Defs} ->
               Core annot ()
clearPatVars
    = do est <- get EST
         traverse deleteDef (allPatVars est)
         pure ()
  where
    deleteDef : Name -> Core annot ()
    deleteDef n = updateDef n (const (Just None))

export
dropTmIn : List (a, (c, d)) -> List (a, d)
dropTmIn = map (\ (n, (_, t)) => (n, t))

-- 'toBind' are the names which are to be implicitly bound (pattern bindings and
-- unbound implicits).
-- Return the names in the order they should be bound: i.e. respecting
-- dependencies between types, and putting @-patterns last because their
-- value is determined from the patterns
export
getToBind : {auto c : Ref Ctxt Defs} -> {auto e : Ref EST (EState vars)} ->
            {auto u : Ref UST (UState annot)} ->
            Env Term vars ->
            Core annot (List (Name, Term vars))
getToBind {vars} env
    = do est <- get EST
         ust <- get UST
         gam <- get Ctxt
         log 7 $ "To bind: " ++ show (map (norm gam) (reverse $ toBind est))
         log 10 $ "With holes " ++ show (map snd (holes ust))
         res <- normImps gam [] (reverse $ toBind est)
         let hnames = map fst res
         log 10 $ "Sorting " ++ show res
         let ret = asLast (map fst (asVariables est)) (depSort hnames res)
         log 7 $ "Sorted implicits " ++ show ret
         pure ret
  where
    -- put the @-pattern bound names last (so that we have the thing they're
    -- equal to bound first)
    asLast : List Name -> List (Name, Term vars) -> 
                          List (Name, Term vars)
    asLast asvars ns 
        = filter (\p => not (fst p `elem` asvars)) ns ++
          filter (\p => fst p `elem` asvars) ns

    norm : Defs -> (Name, Term vars, Term vars) -> (Name, Term vars)
    norm gam (n, tm, ty) = (n, normaliseHoles gam env tm)

    normImps : Defs -> List Name -> List (Name, Term vars, Term vars) -> 
               Core annot (List (Name, Term vars))
    normImps gam ns [] = pure []
    normImps gam ns ((PV n i, tm, ty) :: ts) 
        = if PV n i `elem` ns
             then normImps gam ns ts
             else do rest <- normImps gam (PV n i :: ns) ts
                     pure ((PV n i, normaliseHoles gam env ty) :: rest)
    normImps gam ns ((n, tm, ty) :: ts)
        = case (getFnArgs (normaliseHoles gam env tm)) of
             (Ref nt n', args) => 
                do hole <- isCurrentHole n'
                   if hole && not (n' `elem` ns)
                      then do rest <- normImps gam (n' :: ns) ts
                              pure ((n', normaliseHoles gam env ty) :: rest)
                      -- unified to something concrete, so no longer relevant, drop it
                      else normImps gam ns ts
             _ => do rest <- normImps gam (n :: ns) ts
                     pure ((n, normaliseHoles gam env ty) :: rest)
    
    -- Insert the hole/binding pair into the list before the first thing
    -- which refers to it
    insert : (Name, Term vars) -> List Name -> List Name -> 
             List (Name, Term vars) -> 
             List (Name, Term vars)
    insert h ns sofar [] = [h]
    insert (hn, hty) ns sofar ((hn', hty') :: rest)
        = let used = filter (\n => elem n ns) (toList (getRefs hty')) in
              if hn `elem` used
                 then (hn, hty) :: (hn', hty') :: rest
                 else (hn', hty') :: 
                          insert (hn, hty) ns (hn' :: sofar) rest
    
    -- Sort the list of implicits so that each binding is inserted *after*
    -- all the things it depends on (assumes no cycles)
    depSort : List Name -> List (Name, Term vars) -> 
              List (Name, Term vars)
    depSort hnames [] = []
    depSort hnames (h :: hs) = insert h hnames [] (depSort hnames hs)

substPLet : RigCount -> (n : Name) -> (val : Term vars) -> (ty : Term vars) ->
            Term (n :: vars) -> Term (n :: vars) -> (Term vars, Term vars)
substPLet rig n tm ty sctm scty
    = (Bind n (PLet rig tm ty) sctm, Bind n (PLet rig tm ty) scty)

normaliseHolesScope : Defs -> Env Term vars -> Term vars -> Term vars
normaliseHolesScope defs env (Bind n b sc) 
    = Bind n b (normaliseHolesScope defs 
               -- use Lam because we don't want it reducing in the scope
               (Lam (multiplicity b) Explicit (binderType b) :: env) sc)
normaliseHolesScope defs env tm = normaliseHoles defs env tm

-- Bind implicit arguments, returning the new term and its updated type
bindImplVars : ImplicitMode ->
               Defs ->
               Env Term vars ->
               List (Name, Term vars) ->
               List (Name, RigCount) ->
               Term vars -> Term vars -> (Term vars, Term vars)
bindImplVars NONE gam env args asvs scope scty = (scope, scty)
bindImplVars mode gam env imps asvs scope scty = doBinds 0 env imps scope scty
  where
    -- Replace the name applied to the given number of arguments 
    -- with another term
    repName : Name -> (new : Term vars) -> Term vars -> Term vars
    repName old new (Local r p) = Local r p
    repName old new (Ref nt fn)
        = case nameEq old fn of
               Nothing => Ref nt fn
               Just Refl => new
    repName old new (Bind y b tm) 
        = Bind y (assert_total (map (repName old new) b)) 
                 (repName old (weaken new) tm)
    repName old new (App fn arg) 
        = case getFnArgs (App fn arg) of
               (Ref nt fn', args) =>
                   if old == fn'
                      then let locs = case lookupDefExact fn' (gamma gam) of
                                           Just (Hole i _ _) => i
                                           _ => 0
                                        in
                               apply new (map (repName old new) (drop locs args))
                      else apply (Ref nt fn')
                                 (map (repName old new) args)
               (fn', args) => apply (repName old new fn') 
                                    (map (repName old new) args)
    repName old new (PrimVal y) = PrimVal y
    repName old new Erased = Erased
    repName old new TType = TType
    
    doBinds : Int -> Env Term vars -> List (Name, Term vars) ->
              Term vars -> Term vars -> (Term vars, Term vars)
    doBinds i env [] scope scty = (scope, scty)
    doBinds i env ((n, ty) :: imps) scope scty
      = let (scope', ty') = doBinds (i + 1) env imps scope scty
            tmpN = MN "unb" i
            repNameTm = repName n (Ref Bound tmpN) scope' 
            repNameTy = repName n (Ref Bound tmpN) ty'

            n' = dropNS n in
            case mode of
                 PATTERN =>
                    case lookupDefExact n (gamma gam) of
                         Just (PMDef _ _ _ _) =>
                            -- if n is an accessible pattern variable, bind it,
                            -- otherwise reduce it
                            case n of
                                 PV _ _ =>
                                    -- Need to apply 'n' to the surrounding environment in these cases!
                                    -- otherwise it won't work in nested defs...
                                    let tm = normaliseHolesScope gam env (applyTo (Ref Func n) env) 
                                        rig = maybe RigW id (lookup n asvs) in
                                        substPLet rig n' tm ty 
                                            (refToLocal Nothing tmpN n' repNameTm)
                                            (refToLocal Nothing tmpN n' repNameTy)

                                 _ => let tm = normaliseHolesScope gam env (applyTo (Ref Func n) env) in
                                      (subst tm
                                             (refToLocal Nothing tmpN n repNameTm),
                                       subst tm
                                             (refToLocal Nothing tmpN n repNameTy))
                         _ =>
                            (Bind n' (PVar RigW ty) (refToLocal Nothing tmpN n' repNameTm), 
                             Bind n' (PVTy RigW ty) (refToLocal Nothing tmpN n' repNameTy))
                 -- unless explicitly given, unbound implicits are Rig0
                 PI rig =>
                    case lookupDefExact n (gamma gam) of
                       Just (PMDef _ _ _ _) =>
                          let tm = normaliseHolesScope gam env (applyTo (Ref Func n) env) in
                              (subst tm (refToLocal Nothing tmpN n repNameTm),
                               subst tm (refToLocal Nothing tmpN n repNameTy))
                       _ => (Bind n' (Pi rig Implicit ty) (refToLocal Nothing tmpN n' repNameTm), ty')
                 _ => (Bind n' (Pi RigW Implicit ty) 
                            (refToLocal Nothing tmpN n' repNameTm), ty')

swapElemH : Elem p (x :: y :: ys) -> Elem p (y :: x :: ys)
swapElemH Here = There Here
swapElemH (There Here) = Here
swapElemH (There (There p)) = There (There p)

swapElem : {xs : List a} ->
           Elem p (xs ++ x :: y :: ys) -> Elem p (xs ++ y :: x :: ys)
swapElem {xs = []} prf = swapElemH prf
swapElem {xs = n :: ns} Here = Here
swapElem {xs = n :: ns} (There prf) = There (swapElem prf)

-- We've swapped two binders (in 'push' below) so we'd better swap the
-- corresponding references
swapVars : Term (vs ++ x :: y :: ys) -> Term (vs ++ y :: x :: ys)
swapVars (Local r prf) = Local r (swapElem prf)
swapVars (Ref nt n) = Ref nt n
swapVars {vs} (Bind x b sc) 
    = Bind x (map swapVars b) (swapVars {vs = x :: vs} sc)
swapVars (App fn arg) = App (swapVars fn) (swapVars arg)
swapVars (PrimVal t) = PrimVal t
swapVars Erased = Erased
swapVars TType = TType

-- Push an explicit pi binder as far into a term as it'll go. That is,
-- move it under implicit binders that don't depend on it, and stop
-- when hitting any non-implicit binder
push : (n : Name) -> Binder (Term vs) -> Term (n :: vs) -> Term vs
push n b tm@(Bind (PV x i) (Pi c Implicit ty) sc) -- only push past 'PV's
    = case shrinkTerm ty (DropCons SubRefl) of
           Nothing => -- needs explicit pi, do nothing
                      Bind n b tm
           Just ty' => Bind (PV x i) (Pi c Implicit ty') 
                            (push n (map weaken b) (swapVars {vs = []} sc))
push n b tm = Bind n b tm

-- Move any implicit arguments as far to the left as possible - this helps
-- with curried applications
-- We only do this for variables named 'PV', since they are the unbound
-- implicits, and we don't want to move any given by the programmer
liftImps : ImplicitMode -> (Term vars, Term vars) -> (Term vars, Term vars)
liftImps (PI _) (tm, TType) = (liftImps' tm, TType)
  where
    liftImps' : Term vars -> Term vars
    liftImps' (Bind (PV n i) (Pi c Implicit ty) sc) 
        = Bind (PV n i) (Pi c Implicit ty) (liftImps' sc)
    liftImps' (Bind n (Pi c p ty) sc)
        = push n (Pi c p ty) (liftImps' sc)
    liftImps' tm = tm
liftImps _ x = x

export
bindImplicits : ImplicitMode ->
                Defs -> Env Term vars ->
                List (Name, Term vars) ->
                List (Name, RigCount) ->
                Term vars -> Term vars -> (Term vars, Term vars)
bindImplicits {vars} mode gam env hs asvs tm ty 
   = liftImps mode $ bindImplVars mode gam env (map nHoles hs) asvs
                             (normaliseHolesScope gam env tm)
                             (normaliseHolesScope gam env ty)
  where
    nHoles : (Name, Term vars) -> (Name, Term vars)
    nHoles (n, ty) = (n, normaliseHolesScope gam env ty)
   
export
bindTopImplicits : ImplicitMode -> Defs -> Env Term vars ->
                   List (Name, ClosedTerm) -> 
                   List (Name, RigCount) ->
                   Term vars -> Term vars ->
                   (Term vars, Term vars)
bindTopImplicits {vars} mode gam env hs asvs tm ty
    = bindImplicits mode gam env (map weakenVars hs) asvs tm ty
  where
    weakenVars : (Name, ClosedTerm) -> (Name, Term vars)
    weakenVars (n, tm) = (n, rewrite sym (appendNilRightNeutral vars) in
                                     weakenNs vars tm)

export
renameImplicits : Gamma -> Term vars -> Term vars
renameImplicits gam (Bind (PV n i) b sc) 
    = case lookupDefExact (PV n i) gam of
           Just (PMDef _ _ _ _) =>
--                 trace ("OOPS " ++ show n ++ " = " ++ show def) $
                    Bind n (map (renameImplicits gam) b)
                           (renameImplicits gam (renameTop n sc))
           _ => Bind n (map (renameImplicits gam) b)
                       (renameImplicits gam (renameTop n sc))
renameImplicits gam (Bind n b sc) 
    = Bind n (map (renameImplicits gam) b) (renameImplicits gam sc)
renameImplicits gam t = t

export
convert : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
          {auto e : Ref EST (EState vars)} ->
          annot -> ElabMode -> Env Term vars -> NF vars -> NF vars -> 
          Core annot (List Name)
convert loc elabmode env x y 
    = let umode = case elabmode of
                       InLHS => InLHS
                       _ => InTerm in
          catch (do gam <- get Ctxt
                    log 10 $ "Unifying " ++ show (quote (noGam gam) env x) ++ " and " 
                                         ++ show (quote (noGam gam) env y)
                    hs <- getHoleNames 
                    vs <- unify umode loc env x y
                    hs' <- getHoleNames
                    when (isNil vs && (length hs' < length hs)) $ 
                       solveConstraints umode Normal
                    pure vs)
            (\err => do gam <- get Ctxt 
                        -- Try to solve any remaining constraints to see if it helps
                        -- the error message
                        catch (solveConstraints umode Normal)
                              (\err => pure ())
                        throw (WhenUnifying loc env
                                            (normaliseHoles gam env (quote (noGam gam) env x))
                                            (normaliseHoles gam env (quote (noGam gam) env y))
                                  err))

export
inventFnType : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
               annot -> Env Term vars -> (bname : Name) ->
               Core annot (Term vars, Term (bname :: vars))
inventFnType loc env bname
    = do an <- genName "arg_type"
         scn <- genName "res_type"
         argTy <- addBoundName loc an False env TType
--          scTy <- addBoundName loc scn False (Pi RigW Explicit argTy :: env) TType
         scTy <- addBoundName loc scn False env TType
         pure (argTy, weaken scTy)

-- Given a raw term, collect the explicitly given implicits {x = tm} in the
-- top level application, and return an updated term without them
export
collectGivenImps : RawImp annot -> (RawImp annot, List (Maybe Name, RawImp annot))
collectGivenImps (IImplicitApp loc fn nm arg)
    = let (fn', args') = collectGivenImps fn in
          (fn', (nm, arg) :: args')
collectGivenImps (IApp loc fn arg)
    = let (fn', args') = collectGivenImps fn in
          (IApp loc fn' arg, args')
collectGivenImps tm = (tm, [])

-- try an elaborator, if it fails reset the state and return 'Left',
-- otherwise return 'Right'
export
tryError : {auto c : Ref Ctxt Defs} -> {auto e : Ref UST (UState annot)} ->
           {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
           Core annot a -> Core annot (Either (Error annot) a)
tryError elab 
    = do -- store the current state of everything
         st <- getAllState
         catch (do res <- elab 
                   pure (Right res))
               (\err => do -- reset the state
                           putAllState st
                           pure (Left err))

-- try one elaborator; if it fails, try another
export
try : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
      {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
      Core annot a ->
      Core annot a ->
      Core annot a
try elab1 elab2
    = do Right ok <- tryError elab1
               | Left err => elab2
         pure ok

-- try one elaborator; if it fails, handle the error
export
handle : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
         {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
         Core annot a ->
         (Error annot -> Core annot a) ->
         Core annot a
handle elab1 elab2
    = do -- store the current state of everything
         st <- getAllState
         catch elab1
               (\err => do -- reset the state
                           putAllState st
                           elab2 err)

-- try one (outer) elaborator; if it fails, handle the error. Doesn't
-- save the elaborator state!
export
handleClause
       : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
         {auto i : Ref ImpST (ImpState annot)} ->
         Core annot a ->
         (Error annot -> Core annot a) ->
         Core annot a
handleClause elab1 elab2
    = do -- store the current state of everything
         st <- getState
         catch elab1
               (\err => do -- reset the state
                           putState st
                           elab2 err)

-- try all elaborators, return the results from the ones which succeed
-- and the corresponding elaborator state
export
successful : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
             ElabMode -> List (Maybe Name, Core annot a) ->
             Core annot (List (Either (Maybe Name, Error annot)
                                      (a, AllState vars annot)))
successful elabmode [] = pure []
successful elabmode ((tm, elab) :: elabs)
    = do solveConstraints (case elabmode of
                                InLHS => InLHS
                                _ => InTerm) Normal
         init_st <- getAllState
         Right res <- tryError elab
               | Left err => do rest <- successful elabmode elabs
                                pure (Left (tm, err) :: rest)

         elabState <- getAllState -- save state at end of successful elab
         -- reinitialise state for next elabs
         putAllState init_st
         rest <- successful elabmode elabs
         pure (Right (res, elabState) :: rest)

export
exactlyOne : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
             annot -> Env Term vars -> ElabMode ->
             List (Maybe Name, Core annot (Term vars, Term vars)) ->
             Core annot (Term vars, Term vars)
exactlyOne loc env elabmode [(tm, elab)] = elab
exactlyOne {vars} loc env elabmode all
    = do elabs <- successful elabmode all
         case rights elabs of
              [(res, state)] =>
                   do putAllState state
                      pure res
              rs => throw (altError (lefts elabs) rs)
  where
    normRes : ((Term vars, Term vars), AllState vars annot) -> Term vars
    normRes ((tm, _), thisst) = (normaliseHoles (fst thisst) env tm)

    -- If they've all failed, collect all the errors
    -- If more than one succeeded, report the ambiguity
    altError : List (Maybe Name, Error annot) -> List ((Term vars, Term vars), AllState vars annot) ->
               Error annot
    altError ls [] = AllFailed ls
    altError ls rs = AmbiguousElab loc env (map normRes rs)

export
anyOne : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
         {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
         annot -> ElabMode ->
         List (Maybe Name, Core annot (Term vars, Term vars)) ->
         Core annot (Term vars, Term vars)
anyOne loc elabmode [] = throw (GenericMsg loc "All elaborators failed")
anyOne loc elabmode [(tm, elab)] = elab
anyOne loc elabmode ((tm, e) :: es) 
    = try (do solveConstraints (case elabmode of
                                     InLHS => InLHS
                                     _ => InTerm) Normal
              e) 
          (anyOne loc elabmode es)

-- We run the elaborator in the given environment, but need to end up with a
-- closed term. It'll get substituted into the right place at the end of
-- elaboration, so here we're just lambda binding the names so that the
-- substitution is successful.
total
mkClosedElab : Env Term vars -> 
               (Core annot (Term vars, Term vars)) ->
               Core annot ClosedTerm
mkClosedElab [] elab 
    = do (tm, _) <- elab
         pure tm
mkClosedElab {vars = x :: vars} (b :: env) elab
    = mkClosedElab env 
          (do (sc', _) <- elab
              pure (Bind x (Lam (multiplicity b) Explicit (binderType b)) sc', 
                    Erased))

-- Try the given elaborator; if it fails, and the error matches the
-- predicate, make a hole and try it again later when more holes might
-- have been resolved
export
delayOnFailure : 
      {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
      {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
      annot -> Env Term vars ->
      (expected : Term vars) ->
      (Error annot -> Bool) ->
      (Bool -> Core annot (Term vars, Term vars)) ->
      Core annot (Term vars, Term vars)
delayOnFailure loc env expected pred elab 
    = handle (elab False)
        (\err => do if pred err 
                        then 
                          do (cn, dty) <- addDelayedElab loc env expected
                             log 5 $ "Postponing elaborator for " ++ show expected
                             log 5 $ "New hole type " ++ show cn ++ " : " ++ show dty
                             ust <- get UST
                             put UST (record { delayedElab $= addCtxt cn
                                                 (mkClosedElab env (elab True)) } ust)
                             pure (mkConstantAppFull cn env, expected)
                        else throw err)

export
delayElab : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
            annot -> Env Term vars ->
            (expected : Maybe (Term vars)) ->
            Lazy (Core annot (Term vars, Term vars)) ->
            Core annot (Term vars, Term vars)
delayElab {vars} loc env expected elab
    = do exp <- mkExpected expected
         (cn, dty) <- addDelayedElab loc env exp
         log 5 $ "Postponing elaborator for " ++ show exp
         log 5 $ "New hole type " ++ show cn ++ " : " ++ show dty
         ust <- get UST
         put UST (record { delayedElab $= addCtxt cn
                             (mkClosedElab env elab) } ust)
         pure (mkConstantAppFull cn env, exp)
  where
    mkExpected : Maybe (Term vars) -> Core annot (Term vars)
    mkExpected Nothing
        = do t <- addHole loc env TType
             pure (mkConstantApp t env)
    mkExpected (Just ty) = pure ty

