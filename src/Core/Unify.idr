module Unify

import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT

import Data.List
import Data.List.Views
import Control.ST
import Control.ST.ImplicitCall

%default covering

public export
data Constraint : Type where
     -- An unsolved constraint, noting two terms which need to be convertible
     -- in a particular environment
     MkConstraint : (env : Env Term vars) ->
                    (x : Term vars) -> (y : Term vars) -> 
                    Constraint
     -- An unsolved sequence of constraints, arising from arguments in an
     -- application where solving later constraints relies on solving earlier
     -- ones
     MkSeqConstraint : (env : Env Term vars) ->
                       (xs : List (Term vars)) ->
                       (ys : List (Term vars)) ->
                       Constraint
     -- A resolved constraint
     Resolved : Constraint

-- union : List Name -> List Name -> List Name
-- union cs cs' = nub (cs ++ cs') -- TODO: as a set, not list

-- Currently unsolved constraints - the 'constraints' in the 'Guess'
-- definitions in Gamma refer into this unification state
export
record UnifyState where
     constructor MkUnifyState
     holes : List Name -- unsolved metavariables in gamma (holes and
                       -- guarded constants)
     constraints : Context Constraint -- metavariable constraints 
     nextVar : Int -- next name for checking scopes of binders

initUState : UnifyState
initUState = MkUnifyState [] empty 0

export
UState : Type
UState = State UnifyState

export
setupUnify : ST m Var [add UState]
setupUnify = new initUState

export
doneUnify : (ustate : Var) -> ST m () [remove ustate UState]
doneUnify ustate = delete ustate

export
isHole : (ustate : Var) -> Name -> ST m Bool [ustate ::: UState]
isHole ustate n 
    = do ust <- read ustate
         pure (n `elem` holes ust)

export
getHoleNames : (ustate : Var) -> ST m (List Name) [ustate ::: UState]
getHoleNames ustate
    = do ust <- read ustate
         pure (holes ust)

export
addHoleName : (ustate : Var) -> Name -> ST m () [ustate ::: UState]
addHoleName ustate n
    = do ust <- read ustate
         write ustate (record { holes $= (n ::) } ust)

export
removeHoleName : (ustate : Var) -> Name -> ST m () [ustate ::: UState]
removeHoleName ustate n
    = do ust <- read ustate
         write ustate (record { holes $= filter (/= n) } ust)

export
genName : (ustate : Var) -> String -> ST m Name [ustate ::: UState]
genName ustate root
    = do ust <- read ustate
         write ustate (record { nextVar $= (+1) } ust)
         pure (MN root (nextVar ust))

-- Make a new constant by applying a term to everything in the current
-- environment
mkConstant : Env Term vars -> Term vars -> ClosedTerm
mkConstant [] tm = tm
mkConstant {vars = x :: _} (b :: env) tm 
    = let ty = binderType b in
          mkConstant env (Bind x (Lam ty) tm)

-- Make the type of a new constant which applies a term to everything in
-- the current environment
mkConstantTy : Env Term vars -> Term vars -> ClosedTerm
mkConstantTy [] tm = tm
mkConstantTy {vars = x :: _} (b :: env) tm 
    = let ty = binderType b in
          mkConstant env (Bind x (Pi Explicit ty) tm)

mkConstantAppArgs : Env Term vars -> 
                    List (Term done) -> List (Term (vars ++ done))
mkConstantAppArgs [] xs = xs
mkConstantAppArgs (b :: env) xs 
    = let rec = mkConstantAppArgs env xs in
          Local Here :: map weaken rec

-- Apply a named constant to the current environment.
export
mkConstantApp : Name -> Env Term vars -> Term vars
-- Leftmost argument is the outermost variable, so make a list of local
-- variables then reverse it
mkConstantApp {vars} cn env 
  = let args = reverse (mkConstantAppArgs {done = []} env []) in
        apply (Ref Func cn) (rewrite sym (appendNilRightNeutral vars) in args)

-- Given a term and a type, add a new constant to the global context
-- by applying the term to the current environment
-- Return its name
export
addConstant : CtxtManage m =>
              (ctxt : Var) -> (ustate : Var) ->
              Env Term vars -> 
              (tm : Term vars) -> (ty : Term vars) ->
              (constrs : List Name) ->
              ST m Name [ctxt ::: Defs, ustate ::: UState]
addConstant ctxt ustate env tm ty constrs
    = do let def = mkConstant env tm
         let defty = mkConstantTy env ty
         let guess = MkGlobalDef defty Public (Guess def constrs)
         cn <- genName ustate "p"
         addHoleName ustate cn
         addDef ctxt cn guess
         pure cn

-- Given a type, add a new global metavariable and return its name
export
addHole : CtxtManage m =>
          (ctxt : Var) -> (ustate : Var) ->
          Env Term vars ->
          (ty : Term vars) ->
          ST m Name [ctxt ::: Defs, ustate ::: UState]
addHole ctxt ustate env ty
    = do let defty = mkConstantTy env ty
         let hole = MkGlobalDef defty Public Hole
         cn <- genName ustate "h"
         addHoleName ustate cn
         addDef ctxt cn hole
         pure cn

ufail : CtxtManage m => ST m a []
ufail = throw (GenericMsg "Unification failure")

setConstraint : (ustate : Var) -> Name -> Constraint ->
                ST m () [ustate ::: UState]
setConstraint ustate cname c
    = do ust <- read ustate
         write ustate (record { constraints $= addCtxt cname c } ust)

export
addConstraint : (ctxt : Var) -> (ustate : Var) ->
                Constraint ->        
                ST m Name [ctxt ::: Defs, ustate ::: UState]
addConstraint ctxt ustate constr
    = do c_id <- getNextHole ctxt
         let cn = MN "constraint" c_id
         setConstraint ustate cn constr
         pure cn

public export
interface Unify (tm : List Name -> Type) where
  -- Unify returns a list of names referring to newly added constraints
  unify : CtxtManage m =>
          (ctxt : Var) -> (ustate : Var) ->
          Env Term vars ->
          tm vars -> tm vars -> 
          ST m (List Name) [ctxt ::: Defs, ustate ::: UState]

unifyArgs : (CtxtManage m, Unify tm, Quote tm) =>
            (ctxt : Var) -> (ustate : Var) ->
            Env Term vars ->
            List (tm vars) -> List (tm vars) ->
            ST m (List Name) [ctxt ::: Defs, ustate ::: UState]
unifyArgs ctxt ustate env [] [] = pure []
unifyArgs ctxt ustate env (cx :: cxs) (cy :: cys)
    = do constr <- unify ctxt ustate env cx cy
         case constr of
              [] => unifyArgs ctxt ustate env cxs cys
              _ => do gam <- getCtxt ctxt
                      c <- addConstraint ctxt ustate
                               (MkSeqConstraint env 
                                   (map (quote gam env) (cx :: cxs))
                                   (map (quote gam env) (cy :: cys)))
                      pure [c]
unifyArgs ctxt ustate env _ _ = ufail

postpone : (ctxt : Var) -> (ustate : Var) ->
           Env Term vars ->
           Term vars -> Term vars ->
           ST m (List Name) [ctxt ::: Defs, ustate ::: UState]
postpone ctxt ustate env x y
    = do c <- addConstraint ctxt ustate
                   (MkConstraint env x y)
         pure [c]

-- Get the variables in an application argument list; fail if any arguments 
-- are not variables, fail if there's any repetition of variables
-- We use this to check that the pattern unification rule is applicable
-- when solving a metavariable applied to arguments
getVars : List (NF vars) -> Maybe (List (x ** Elem x vars))
getVars [] = Just []
getVars (NApp (NLocal v) [] :: xs) 
    = if vIn xs then Nothing
         else do xs' <- getVars xs
                 pure ((_ ** v) :: xs')
  where
    -- Check the variable doesn't appear later
    vIn : List (NF vars) -> Bool
    vIn [] = False
    vIn (NApp (NLocal el') [] :: xs)
        = if sameVar v el' then True else vIn xs
    vIn (_ :: xs) = vIn xs
getVars (_ :: xs) = Nothing

-- Make a sublist representing the variables used in the application.
-- We'll use this to ensure that local variables which appear in a term
-- are all arguments to a metavariable application for pattern unification
toSubVars : (vars : List Name) -> List (x ** Elem x vars) ->
            (newvars ** SubVars newvars vars)
toSubVars [] xs = ([] ** SubRefl)
toSubVars (n :: ns) xs 
     -- If there's a proof 'Here' in 'xs', then 'n' should be kept,
     -- otherwise dropped
     -- (Remember: 'n' might be shadowed; looking for 'Here' ensures we
     -- get the *right* proof that the name is in scope!)
     = let (_ ** svs) = toSubVars ns (dropHere xs) in
           if anyHere xs 
              then (_ ** KeepCons svs)
              else (_ ** DropCons svs)
  where
    anyHere : List (x ** Elem x (n :: ns)) -> Bool
    anyHere [] = False
    anyHere ((_ ** Here) :: xs) = True
    anyHere ((_ ** There p) :: xs) = anyHere xs

    dropHere : List (x ** Elem x (n :: ns)) -> List (x ** Elem x ns) 
    dropHere [] = []
    dropHere ((_ ** Here) :: xs) = dropHere xs
    dropHere ((_ ** There p) :: xs) = (_ ** p) :: dropHere xs

{- Applying the pattern unification rule is okay if:
   * Arguments are all distinct local variables
   * The metavariable name doesn't appear in the unifying term
   * The local variables which appear in the term are all arguments to
     the metavariable application (not checked here, checked with the
     result of `patternEnv`

   Return the subset of the environment used in the arguments
   to which the metavariable is applied. If this environment is enough
   to check the term we're unifying with, and that term doesn't use the
   metavariable name, we can safely apply the rule.
-}
patternEnv : (ctxt : Var) -> (ustate : Var) ->
            Env Term vars -> List (Closure vars) -> 
            ST m (Maybe (newvars ** SubVars newvars vars))
                 [ctxt ::: Defs, ustate ::: UState]
patternEnv ctxt ustate env args
    = do gam <- getCtxt ctxt
         let args' = map (evalClosure gam) args
         case getVars args' of
              Nothing => pure Nothing
              Just vs => pure (Just (toSubVars _ vs))

-- Instantiate a metavariable by binding the variables in 'newvars'
-- and returning the term
-- If the type of the metavariable doesn't have enough arguments, fail, because
-- this wasn't valid for pattern unification
instantiate : CtxtManage m =>
              (ctxt : Var) -> (ustate : Var) ->
              (metavar : Name) -> SubVars newvars vars -> Term newvars ->
              ST m () [ctxt ::: Defs, ustate ::: UState]
instantiate ctxt ustate metavar smvs tm {newvars}
     = do gam <- getCtxt ctxt
          case lookupDefTy metavar gam of
               Nothing => ufail
               Just (_, ty) => 
                    case mkRHS [] newvars CompatPre ty 
                             (rewrite appendNilRightNeutral newvars in tm) of
                         Nothing => ufail
                         Just rhs => 
                            do let soln = MkGlobalDef ty Public 
                                               (PMDef [] (STerm rhs))
                               addDef ctxt metavar soln
                               removeHoleName ustate metavar
  where
    mkRHS : (got : List Name) -> (newvars : List Name) ->
            CompatibleVars got rest ->
            Term rest -> Term (newvars ++ got) -> Maybe (Term rest)
    mkRHS got ns cvs ty tm with (snocList ns)
      mkRHS got [] cvs ty tm | Empty = Just (renameVars cvs tm)
      mkRHS got (ns ++ [n]) cvs (Bind x (Pi _ ty) sc) tm | (Snoc rec) 
           = do sc' <- mkRHS (n :: got) ns (CompatExt cvs) sc 
                           (rewrite appendAssociative ns [n] got in tm)
                pure (Bind x (Lam ty) sc')
      -- Run out of variables to bind
      mkRHS got (ns ++ [n]) cvs ty tm | (Snoc rec) = Nothing

mutual
  unifyApp : CtxtManage m =>
             (ctxt : Var) -> (ustate : Var) ->
             Env Term vars ->
             NHead vars -> List (Closure vars) -> NF vars ->
             ST m (List Name) [ctxt ::: Defs, ustate ::: UState]
  unifyApp ctxt ustate env (NRef nt var) args tm 
      = case !(patternEnv ctxt ustate env args) of
           Just (newvars ** submv) =>
                do gam <- getCtxt ctxt
                   -- newvars and args should be the same length now, because
                   -- there's one new variable for each distinct argument.
                   -- The types don't express this, but 'submv' at least
                   -- tells us that 'newvars' are the subset of 'vars'
                   -- being applied to the metavariable, and so 'tm' must
                   -- only use those variables for success
                   case shrinkTerm (quote gam env tm) submv of
                        Nothing => ufail
                        Just tm' => do instantiate ctxt ustate var submv tm'
                                       pure []
           Nothing => postpone ctxt ustate env 
                         (quote empty env (NApp (NRef nt var) args))
                         (quote empty env tm)
  unifyApp ctxt ustate env hd args (NApp hd' args')
      = postpone ctxt ustate env
                 (quote empty env (NApp hd args)) 
                 (quote empty env (NApp hd' args'))
  -- If they're already convertible without metavariables, we're done,
  -- otherwise postpone
  unifyApp ctxt ustate env hd args tm 
      = do gam <- getCtxt ctxt
           if convert gam env (quote empty env (NApp hd args))
                              (quote empty env tm)
              then pure []
              else postpone ctxt ustate env
                         (quote empty env (NApp hd args)) (quote empty env tm)

  export
  Unify Closure where
    unify ctxt ustate env x y 
        = do gam <- getCtxt ctxt
             -- 'quote' using an empty global context, because then function
             -- names won't reduce until they have to
             let x' = quote empty env x
             let y' = quote empty env y
             unify ctxt ustate env x' y'

  export
  Unify NF where
    unify ctxt ustate env (NBind x (Pi ix tx) scx) (NBind y (Pi iy ty) scy) 
        = if ix /= iy
             then ufail
             else
               do ct <- unify ctxt ustate env tx ty
                  xn <- genName ustate "x"
                  let env' : TT.Env.Env Term (x :: _)
                           = Pi ix (quote empty env tx) :: env
                  case ct of
                       [] => -- no constraints, check the scope
                             do let tscx = scx (toClosure env (Ref Bound xn))
                                let tscy = scy (toClosure env (Ref Bound xn))
                                let termx = refToLocal xn x (quote empty env tscx)
                                let termy = refToLocal xn x (quote empty env tscy)
                                unify ctxt ustate env' termx termy
                       cs => -- constraints, make new guarded constant
                             do let txtm = quote empty env tx
                                let tytm = quote empty env ty
                                c <- addConstant ctxt ustate env
                                       (Bind x (Lam txtm) (Local Here))
                                       (Bind x (Pi Explicit txtm)
                                           (weaken tytm)) cs
                                let tscx = scx (toClosure env (Ref Bound xn))
                                let tscy = scy (toClosure env 
                                               (App (mkConstantApp c env) (Ref Bound xn)))
                                let termx = refToLocal xn x (quote empty env tscx)
                                let termy = refToLocal xn x (quote empty env tscy)
                                cs' <- unify ctxt ustate env' termx termy
                                pure (union cs cs')
{- -- probably not...
    unify ctxt ustate env (NBind x (Lam tx) scx) (NBind y (Lam ty) scy) 
       = do ct <- unify ctxt ustate env tx ty
            xn <- genName ustate "x"
            let env' : TT.Env.Env Term (x :: _)
                     = Lam (quote empty env tx) :: env
            case ct of
                 [] => -- no constraints, check the scope
                       do let tscx = scx (toClosure env (Ref Bound xn))
                          let tscy = scy (toClosure env (Ref Bound xn))
                          let termx = refToLocal xn x (quote empty env tscx)
                          let termy = refToLocal xn x (quote empty env tscy)
                          unify ctxt ustate env' termx termy
                 cs => -- constraints, make new guarded constant
                       do let txtm = quote empty env tx
                          let tytm = quote empty env ty
                          c <- addConstant ctxt ustate env
                                 (Bind x (Lam txtm) (Local Here))
                                 (Bind x (Pi Explicit txtm)
                                     (weaken tytm)) cs
                          let tscx = scx (toClosure env (Ref Bound xn))
                          let tscy = scy (toClosure env 
                                         (App (mkConstantApp c env) (Ref Bound xn)))
                          let termx = refToLocal xn x (quote empty env tscx)
                          let termy = refToLocal xn x (quote empty env tscy)
                          cs' <- unify ctxt ustate env' termx termy
                          pure (union cs cs')
-}
    unify ctxt ustate env (NApp hd args) y 
        = unifyApp ctxt ustate env hd args y
    unify ctxt ustate env y (NApp hd args)
        = unifyApp ctxt ustate env hd args y
    unify ctxt ustate env (NDCon x tagx ax xs) (NDCon y tagy ay ys)
        = if tagx == tagy
             then unifyArgs ctxt ustate env xs ys
             else ufail
    unify ctxt ustate env (NTCon x tagx ax xs) (NTCon y tagy ay ys)
        = if tagx == tagy
             then unifyArgs ctxt ustate env xs ys
             else ufail
    unify ctxt ustate env (NPrimVal x) (NPrimVal y) 
        = if x == y 
             then pure [] 
             else ufail
    unify ctxt ustate env x NErased = pure []
    unify ctxt ustate env NErased y = pure []
    unify ctxt ustate env NType NType = pure []
    unify ctxt ustate env x y 
        = do gam <- getCtxt ctxt
             if convert gam env x y
                then pure []
                else ufail

  export
  Unify Term where
    -- TODO: Don't just go to values, try to unify the terms directly
    -- and avoid normalisation as far as possible
    unify ctxt ustate env x y 
          = do gam <- getCtxt ctxt
               unify ctxt ustate env (nf gam env x) (nf gam env y)

-- Try again to solve the given named constraint, and return the list
-- of constraint names are generated when trying to solve it.
export
retry : CtxtManage m =>
        (ctxt : Var) -> (ustate : Var) ->
        (cname : Name) -> ST m (List Name) [ctxt ::: Defs, ustate ::: UState]
retry ctxt ustate cname
    = do ust <- read ustate
         case lookupCtxt cname (constraints ust) of
              Nothing => throw (GenericMsg ("No such constraint " ++ show cname))
              -- If the constraint is now resolved (i.e. unifying now leads
              -- to no new constraints) replace it with 'Resolved' in the
              -- constraint context so we don't do it again
              Just Resolved => pure []
              Just (MkConstraint env x y) =>
                   do cs <- unify ctxt ustate env x y
                      case cs of
                           [] => do setConstraint ustate cname Resolved
                                    pure cs
                           _ => pure cs
              Just (MkSeqConstraint env xs ys) =>
                   do cs <- unifyArgs ctxt ustate env xs ys
                      case cs of
                           [] => do setConstraint ustate cname Resolved
                                    pure cs
                           _ => pure cs

retryHole : CtxtManage m =>
            (ctxt : Var) -> (ustate : Var) ->
            (hole : Name) ->
            ST m () [ctxt ::: Defs, ustate ::: UState]
retryHole ctxt ustate hole
    = do gam <- getCtxt ctxt
         case lookupDef hole gam of
              Nothing => throw (GenericMsg ("No such hole " ++ show hole))
              Just (Guess tm constraints) => 
                   do cs' <- mapST (retry ctxt ustate) constraints
                      case concat cs' of
                           -- All constraints resolved, so turn into a
                           -- proper definition and remove it from the
                           -- hole list
                           [] => do updateDef ctxt hole (PMDef [] (STerm tm))
                                    removeHoleName ustate hole
                           newcs => updateDef ctxt hole (Guess tm newcs)
              Just _ => pure () -- Nothing we can do

-- Attempt to solve any remaining constraints in the unification context.
-- Do this by working through the list of holes
-- On encountering a 'Guess', try the constraints attached to it 
export
solveConstraints : CtxtManage m =>
                   (ctxt : Var) -> (ustate : Var) ->
                   ST m () [ctxt ::: Defs, ustate ::: UState]
solveConstraints ctxt ustate 
    = do hs <- getHoleNames ustate
         mapST (retryHole ctxt ustate) hs
         -- Question: Another iteration if any holes have been resolved?
         pure ()

dumpHole : CtxtManage m =>
           (ctxt : Var) -> (ustate : Var) ->
           (hole : Name) ->
           ST m () [ctxt ::: Defs, ustate ::: UState]
dumpHole ctxt ustate hole
    = do gam <- getCtxt ctxt
         case lookupDefTy hole gam of
              Nothing => throw (GenericMsg ("No such hole " ++ show hole))
              Just (Guess tm constraints, ty) => 
                   do putStrLn $ "!" ++ show hole ++ " : " ++ show ty
                      mapST dumpConstraint constraints 
                      pure ()
              Just (_, ty) =>
                   putStrLn $ "?" ++ show hole ++ " : " ++ show ty
  where
    dumpConstraint : ConsoleIO m => Name -> ST m () [ctxt ::: Defs, ustate ::: UState]
    dumpConstraint n
        = do ust <- read ustate
             gam <- getCtxt ctxt
             case lookupCtxt n (constraints ust) of
                  Nothing => pure ()
                  Just Resolved => putStrLn "\tResolved"
                  Just (MkConstraint env x y) =>
                       putStrLn $ "\t" ++ show (normalise gam env x) 
                                      ++ " =?= " ++ show (normalise gam env y)
                  Just (MkSeqConstraint _ xs ys) =>
                       putStrLn $ "\t" ++ show xs ++ " =?= " ++ show ys

export
dumpConstraints : CtxtManage m =>
                  (ctxt : Var) -> (ustate : Var) ->
                  ST m () [ctxt ::: Defs, ustate ::: UState]
dumpConstraints ctxt ustate
    = do hs <- getHoleNames ustate
         mapST (dumpHole ctxt ustate) hs
         pure ()

