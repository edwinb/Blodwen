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
     logLevel : Nat
     holes : List Name -- unsolved metavariables in gamma (holes and
                       -- guarded constants)
     currentHoles : List Name -- unsolved metavariables in this session
     constraints : Context (Constraint annot) -- metavariable constraints 
     dotConstraints : List (Constraint annot) -- dot pattern constraints
                          -- after elaboration, we check that the equations
                          -- are already solved, which shows that the term
                          -- in the pattern is valid by unification

export
initUState : UnifyState annot
initUState = MkUnifyState 0 [] [] empty []

public export
UState : Type -> Type
UState = UnifyState

-- A label for unification state in the global state
export
data UST : Type where

export
setLogLevel : {auto u : Ref UST (UState annot)} ->
              Nat -> Core annot ()
setLogLevel n
    = do ust <- get UST
         put UST (record { logLevel = n } ust)

export
log : {auto u : Ref UST (UState annot)} ->
      Nat -> Lazy String -> Core annot ()
log lvl str
    = do ust <- get UST
         if logLevel ust >= lvl
            then coreLift $ putStrLn $ "LOG " ++ show lvl ++ ": " ++ str
            else pure ()

export
isHole : {auto u : Ref UST (UState annot)} ->
         Name -> Core annot Bool
isHole n 
    = do ust <- get UST
         pure (n `elem` holes ust)

export
getHoleNames : {auto u : Ref UST (UState annot)} ->
               Core annot (List Name)
getHoleNames 
    = do ust <- get UST
         pure (holes ust)

export
getCurrentHoleNames : {auto u : Ref UST (UState annot)} ->
                      Core annot (List Name)
getCurrentHoleNames 
    = do ust <- get UST
         pure (currentHoles ust)

export
resetHoles : {auto u : Ref UST (UState annot)} ->
             Core annot ()
resetHoles 
    = do ust <- get UST
         -- TODO: Also clear out solved/ImpBind holes
         put UST (record { currentHoles = [] } ust)

export
addHoleName : {auto u : Ref UST (UState annot)} ->
              Name -> Core annot ()
addHoleName n
    = do ust <- get UST
         put UST (record { holes $= (n ::),
                           currentHoles $= (n ::) } ust)

dropFirst : Eq a => a -> List a -> List a
dropFirst x [] = []
dropFirst x (y :: ys) = if x == y then ys else y :: dropFirst x ys

export
removeHoleName : {auto u : Ref UST (UState annot)} ->
                 Name -> Core annot ()
removeHoleName n
    = do ust <- get UST
         put UST (record { holes $= dropFirst n,
                           currentHoles $= dropFirst n } ust)

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

-- Given a term and a type, add a new guarded constant to the global context
-- by applying the term to the current environment
-- Return its name
export
addConstant : {auto u : Ref UST (UState annot)} ->
              {auto c : Ref Ctxt Defs} ->
              Env Term vars -> 
              (tm : Term vars) -> (ty : Term vars) ->
              (constrs : List Name) ->
              Core annot Name
addConstant env tm ty constrs
    = do let def = mkConstant env tm
         let defty = mkConstantTy env ty
         let guess = newDef defty Public (Guess def constrs)
         cn <- genName "p"
         addHoleName cn
         addDef cn guess
         pure cn

-- Given a type and a name, add a new global metavariable
export
addNamedHole : {auto u : Ref UST (UState annot)} ->
               {auto c : Ref Ctxt Defs} ->
               Name -> (patvar : Bool) -> Env Term vars ->
               (ty : Term vars) -> Core annot ()
addNamedHole cn patvar env ty
    = do let defty = mkConstantTy env ty
         let hole = newDef defty Public (Hole (length env) patvar)
         addHoleName cn
         addDef cn hole

-- Given a type, add a new global metavariable and return its name
export
addHole : {auto u : Ref UST (UState annot)} ->
          {auto c : Ref Ctxt Defs} ->       
          Env Term vars ->
          (ty : Term vars) -> Core annot Name
addHole env ty
    = do cn <- genName "h"
         addNamedHole cn False env ty
         pure cn

export
addBoundName : {auto u : Ref UST (UState annot)} ->
               {auto c : Ref Ctxt Defs} ->
               Name -> (patvar : Bool) -> Env Term vars ->
               (ty : Term vars) -> Core annot (Term vars)
addBoundName n patvar env exp
    = do addNamedHole n patvar env exp
         pure (mkConstantApp n env)

export
setConstraint : {auto u : Ref UST (UState annot)} ->
                Name -> Constraint annot ->
                Core annot ()
setConstraint cname c
    = do ust <- get UST
         put UST (record { constraints $= addCtxt cname c } ust)

export
addConstraint : {auto u : Ref UST (UState annot)} ->
                {auto c : Ref Ctxt Defs} ->
                Constraint annot -> Core annot Name
addConstraint constr
    = do c_id <- getNextHole
         let cn = MN "constraint" c_id
         setConstraint cn constr
         pure cn

export
addDot : {auto u : Ref UST (UState annot)} ->
         annot -> Env Term vars -> Term vars -> Term vars ->
         Core annot ()
addDot loc env x y
    = do ust <- get UST
         put UST (record { dotConstraints $= ((MkConstraint loc env x y) ::) }
                         ust)

export
dumpHole : {auto u : Ref UST (UState annot)} ->
           {auto c : Ref Ctxt Defs} ->
           (loglevel : Nat) -> (hole : Name) -> Core annot ()
dumpHole lvl hole
    = do ust <- get UST
         if logLevel ust < lvl
            then pure ()
            else do
               gam <- getCtxt
               case lookupDefTyExact hole gam of
                    Nothing => pure ()
                    Just (Guess tm constraints, ty) => 
                         do log lvl $ "!" ++ show hole ++ " : " ++ 
                                              show (normaliseHoles gam [] ty)
                            log lvl $ "\t  = " ++ show (normaliseHoles gam [] tm)
                                            ++ "\n\twhen"
                            traverse (\x => dumpConstraint x) constraints 
                            pure ()
                    Just (Hole _ _, ty) =>
                         log lvl $ "?" ++ show hole ++ " : " ++ 
                                           show (normaliseHoles gam [] ty)
                    Just (PMDef _ args t, ty) =>
                         log 4 $ "Solved: " ++ show hole ++ " : " ++ 
                                       show (normalise gam [] ty) ++
                                       " = " ++ show t
                    Just (ImpBind, ty) =>
                         log 4 $ "Bound: " ++ show hole ++ " : " ++ 
                                       show (normalise gam [] ty)
                    _ => pure ()
  where
    dumpConstraint : Name -> Core annot ()
    dumpConstraint n
        = do ust <- get UST
             gam <- getCtxt
             case lookupCtxtExact n (constraints ust) of
                  Nothing => pure ()
                  Just Resolved => log lvl "\tResolved"
                  Just (MkConstraint _ env x y) =>
                    do log lvl $ "\t  " ++ show (normalise gam env x) 
                                      ++ " =?= " ++ show (normalise gam env y)
                       log 5 $ "\t    from " ++ show x 
                                      ++ " =?= " ++ show y
                  Just (MkSeqConstraint _ _ xs ys) =>
                       log lvl $ "\t\t" ++ show xs ++ " =?= " ++ show ys

export
dumpConstraints : {auto u : Ref UST (UState annot)} -> 
                  {auto c : Ref Ctxt Defs} ->
                  (loglevel : Nat) ->
                  (all : Bool) ->
                  Core annot ()
dumpConstraints loglevel all
    = do hs <- if all then getHoleNames else getCurrentHoleNames
         case hs of
              [] => pure ()
              _ => do log loglevel "--- CONSTRAINTS AND HOLES ---"
                      traverse (dumpHole loglevel) hs
                      pure ()

export
dumpDots : {auto u : Ref UST (UState annot)} ->
           {auto c : Ref Ctxt Defs} ->
           Core annot ()
dumpDots
    = do ust <- get UST
         log 2 "--- DOT PATTERN CONSTRAINTS ---"
         gam <- getCtxt
         traverse (dumpConstraint gam) (dotConstraints ust)
         pure ()
  where
    dumpConstraint : Gamma -> Constraint annot -> Core annot ()
    dumpConstraint gam (MkConstraint _ env x y)
        = do log 2 $ "\t  " ++ show (normalise gam env x) 
                            ++ " =?= " ++ show (normalise gam env y)
             log 5 $ "\t    from " ++ show x 
                            ++ " =?= " ++ show y
    dumpConstraint gam _ = pure ()

export
checkDots : {auto u : Ref UST (UState annot)} ->
            {auto c : Ref Ctxt Defs} ->
            Core annot ()
checkDots
    = do ust <- get UST
         gam <- getCtxt
         traverse (checkConstraint gam) (dotConstraints ust)
         put UST (record { dotConstraints = [] } ust)
         pure ()
  where
    checkConstraint : Gamma -> Constraint annot -> Core annot ()
    checkConstraint gam (MkConstraint loc env x y)
        = if convert gam env x y
             then pure ()
             else throw (BadDotPattern loc x y)
    checkConstraint game _ = pure ()

