module Core.UnifyState

import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT

import Data.List
import Data.List.Views

%default covering

public export
data Constraint : Type -> Type where
     -- An unsolved constraint, noting two terms which need to be convertible
     -- in a particular environment
     MkConstraint : annot -> 
                    (env : Env Term vars) ->
                    (x : Term vars) -> (y : Term vars) -> 
                    Constraint annot
     -- An unsolved sequence of constraints, arising from arguments in an
     -- application where solving later constraints relies on solving earlier
     -- ones
     MkSeqConstraint : annot ->
                       (env : Env Term vars) ->
                       (xs : List (Term vars)) ->
                       (ys : List (Term vars)) ->
                       Constraint annot
     -- A resolved constraint
     Resolved : Constraint annot

-- union : List Name -> List Name -> List Name
-- union cs cs' = nub (cs ++ cs') -- TODO: as a set, not list

-- Currently unsolved constraints - the 'constraints' in the 'Guess'
-- definitions in Gamma refer into this unification state
public export
record UnifyState annot where
     constructor MkUnifyState
     holes : List Name -- unsolved metavariables in gamma (holes and
                       -- guarded constants)
     currentHoles : List Name -- unsolved metavariables in this session
     constraints : Context (Constraint annot) -- metavariable constraints 

initUState : UnifyState annot
initUState = MkUnifyState [] [] empty

public export
UState : Type -> Type
UState = UnifyState

-- A label for unification state in the global state
export
data UST : Type where

export
setupUnify : CoreM annot [] [UST ::: UState annot] ()
setupUnify = new UST initUState

export
doneUnify : CoreM annot [UST ::: UState annot] [] ()
doneUnify = delete UST

export
isHole : Name -> Core annot [UST ::: UState annot] Bool
isHole n 
    = do ust <- get UST
         pure (n `elem` holes ust)

export
getHoleNames : Core annot [UST ::: UState annot] (List Name)
getHoleNames 
    = do ust <- get UST
         pure (holes ust)

export
getCurrentHoleNames : Core annot [UST ::: UState annot] (List Name)
getCurrentHoleNames 
    = do ust <- get UST
         pure (currentHoles ust)

export
resetHoles : Core annot [UST ::: UState annot] ()
resetHoles 
    = do ust <- get UST
         put UST (record { currentHoles = [] } ust)

export
addHoleName : Name -> Core annot [UST ::: UState annot] ()
addHoleName n
    = do ust <- get UST
         put UST (record { holes $= (n ::),
                             currentHoles $= (n ::) } ust)

export
removeHoleName : Name -> Core annot [UST ::: UState annot] ()
removeHoleName n
    = do ust <- get UST
         put UST (record { holes $= filter (/= n) } ust)

-- Make a new constant by applying a term to everything in the current
-- environment
mkConstant : Env Term vars -> Term vars -> ClosedTerm
mkConstant [] tm = tm
mkConstant {vars = x :: _} (b :: env) tm 
    = let ty = binderType b in
          mkConstant env (Bind x (Lam Explicit ty) tm)

-- Make the type of a new constant which applies a term to everything in
-- the current environment
mkConstantTy : Env Term vars -> Term vars -> ClosedTerm
mkConstantTy = abstractEnvType

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
addConstant : Env Term vars -> 
              (tm : Term vars) -> (ty : Term vars) ->
              (constrs : List Name) ->
              Core annot [Ctxt ::: Defs, UST ::: UState annot] Name
addConstant env tm ty constrs
    = do let def = mkConstant env tm
         let defty = mkConstantTy env ty
         let guess = newDef defty Public (Guess def constrs)
         cn <- genName "p"
         addHoleName cn
         addDef cn guess
         pure cn

-- Given a type, add a new global metavariable and return its name
export
addNamedHole : Name -> Env Term vars ->
               (ty : Term vars) ->
               Core annot [Ctxt ::: Defs, UST ::: UState annot] ()
addNamedHole cn env ty
    = do let defty = mkConstantTy env ty
         let hole = newDef defty Public (Hole (length env))
         addHoleName cn
         addDef cn hole

-- Given a type, add a new global metavariable and return its name
export
addHole : Env Term vars ->
          (ty : Term vars) ->
          Core annot [Ctxt ::: Defs, UST ::: UState annot] Name
addHole env ty
    = do cn <- genName "h"
         addNamedHole cn env ty
         pure cn

export
addBoundName : Name -> Env Term vars ->
               (ty : Term vars) ->
               Core annot [Ctxt ::: Defs, UST ::: UState annot] (Term vars)
addBoundName n env exp
    = do addNamedHole n env exp
         pure (mkConstantApp n env)

export
setConstraint : Name -> Constraint annot ->
                Core annot [UST ::: UState annot] ()
setConstraint cname c
    = do ust <- get UST
         put UST (record { constraints $= addCtxt cname c } ust)

export
addConstraint : Constraint annot ->        
                Core annot [Ctxt ::: Defs, UST ::: UState annot] Name
addConstraint constr
    = do c_id <- getNextHole
         let cn = MN "constraint" c_id
         setConstraint cn constr
         pure cn

export
dumpHole : (hole : Name) -> Core annot [Ctxt ::: Defs, UST ::: UState annot] ()
dumpHole hole
    = do gam <- getCtxt
         case lookupDefTy hole gam of
              Nothing => pure ()
              Just (Guess tm constraints, ty) => 
                   do putStrLn $ "!" ++ show hole ++ " : " ++ 
                                        show (normalise gam [] ty)
                      traverse (\x => dumpConstraint x) constraints 
                      pure ()
              Just (Hole _, ty) =>
                   putStrLn $ "?" ++ show hole ++ " : " ++ 
                                     show (normalise gam [] ty)
--               Just (PMDef _ args t, ty) =>
--                    putStrLn $ "Solved: " ++ show hole ++ " : " ++ 
--                                  show (normalise gam [] ty) ++
--                                  " = " ++ show t
--               Just (ImpBind, ty) =>
--                    putStrLn $ "Bound: " ++ show hole ++ " : " ++ 
--                                  show (normalise gam [] ty)
              _ => pure ()
  where
    dumpConstraint : Name -> Core annot [Ctxt ::: Defs, UST ::: UState annot] ()
    dumpConstraint n
        = do ust <- get UST
             gam <- getCtxt
             case lookupCtxt n (constraints ust) of
                  Nothing => pure ()
                  Just Resolved => putStrLn "\tResolved"
                  Just (MkConstraint _ env x y) =>
                       putStrLn $ "\t" ++ show (normalise gam env x) 
                                      ++ " =?= " ++ show (normalise gam env y)
                  Just (MkSeqConstraint _ _ xs ys) =>
                       putStrLn $ "\t" ++ show xs ++ " =?= " ++ show ys

export
dumpConstraints : Core annot [Ctxt ::: Defs, UST ::: UState annot] ()
dumpConstraints 
    = do hs <- getCurrentHoleNames
         traverse (\x => dumpHole x) hs
         pure ()

