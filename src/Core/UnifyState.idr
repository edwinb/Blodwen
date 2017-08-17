module Core.UnifyState

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
public export
record UnifyState where
     constructor MkUnifyState
     holes : List Name -- unsolved metavariables in gamma (holes and
                       -- guarded constants)
     currentHoles : List Name -- unsolved metavariables in this session
     constraints : Context Constraint -- metavariable constraints 
     nextVar : Int -- next name for checking scopes of binders

initUState : UnifyState
initUState = MkUnifyState [] [] empty 0

public export
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
getCurrentHoleNames : (ustate : Var) -> ST m (List Name) [ustate ::: UState]
getCurrentHoleNames ustate
    = do ust <- read ustate
         pure (currentHoles ust)

export
resetHoles : (ustate : Var) -> ST m () [ustate ::: UState]
resetHoles ustate
    = do ust <- read ustate
         write ustate (record { currentHoles = [] } ust)

export
addHoleName : (ustate : Var) -> Name -> ST m () [ustate ::: UState]
addHoleName ustate n
    = do ust <- read ustate
         write ustate (record { holes $= (n ::),
                                currentHoles $= (n ::) } ust)

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
          mkConstantTy env (Bind x (Pi Explicit ty) tm)

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
         let guess = newDef defty Public (Guess def constrs)
         cn <- genName ustate "p"
         addHoleName ustate cn
         addDef ctxt cn guess
         pure cn

-- Given a type, add a new global metavariable and return its name
addNamedHole : CtxtManage m =>
               (ctxt : Var) -> (ustate : Var) ->
               Name ->
               Env Term vars ->
               (ty : Term vars) ->
               ST m () [ctxt ::: Defs, ustate ::: UState]
addNamedHole ctxt ustate cn env ty
    = do let defty = mkConstantTy env ty
         let hole = newDef defty Public Hole
         addHoleName ustate cn
         putStrLn $ "Added hole " ++ show cn ++ " : " ++ show defty
         addDef ctxt cn hole

-- Given a type, add a new global metavariable and return its name
export
addHole : CtxtManage m =>
          (ctxt : Var) -> (ustate : Var) ->
          Env Term vars ->
          (ty : Term vars) ->
          ST m Name [ctxt ::: Defs, ustate ::: UState]
addHole ctxt ustate env ty
    = do cn <- genName ustate "h"
         addNamedHole ctxt ustate cn env ty
         pure cn

export
addBoundName : CtxtManage m =>
               (ctxt : Var) -> (ustate : Var) ->
               Name -> Env Term vars ->
               (ty : Term vars) ->
               ST m (Term vars) [ctxt ::: Defs, ustate ::: UState]
addBoundName ctxt ustate n env exp
    = do addNamedHole ctxt ustate n env exp
         pure (mkConstantApp n env)

export
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

