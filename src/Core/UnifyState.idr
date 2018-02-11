module Core.UnifyState

import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT
import Core.TTC
import Utils.Binary

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

export
TTC annot annot => TTC annot (Constraint annot) where
  toBuf b (MkConstraint {vars} x env tm y) 
      = do tag 0; toBuf b vars; toBuf b x; toBuf b env; toBuf b tm; toBuf b y
  toBuf b (MkSeqConstraint {vars} x env xs ys) 
      = do tag 1; toBuf b vars; toBuf b x; toBuf b env; toBuf b xs; toBuf b ys
  toBuf b Resolved = tag 2

  fromBuf s b 
      = case !getTag of
             0 => do vars <- fromBuf s b
                     x <- fromBuf s b; env <- fromBuf s b;
                     tm <- fromBuf s b; y <- fromBuf s b
                     pure (MkConstraint {vars} x env tm y)
             1 => do vars <- fromBuf s b
                     x <- fromBuf s b; env <- fromBuf s b;
                     xs <- fromBuf s b; ys <- fromBuf s b
                     pure (MkSeqConstraint {vars} x env xs ys)
             2 => pure Resolved
             _ => corrupt "Constraint"

-- Currently unsolved constraints - the 'constraints' in the 'Guess'
-- definitions in Gamma refer into this unification state
-- "session" refers to the current top level elaborator call (so the current
-- term being elaborated)
public export
record UnifyState annot where
     constructor MkUnifyState
     logLevel : Nat
     holes : List (annot, Name)
            -- unsolved metavariables in gamma (holes and guarded constants)
            -- along with where they were introduced
     currentHoles : List Name -- unsolved metavariables in this session
     delayedHoles : List Name -- unsolved metavariables which must be resolved 
                              -- but not necessarily in
                              -- the current session (any time later in the
                              -- source file is okay)
                              -- Differs from 'holes' in that holes may
                              -- contain named holes given by the user and
                              -- their dependencies, which don't have to be 
                              -- resolved
     constraints : Context (Constraint annot) -- metavariable constraints 
     dotConstraints : List (Constraint annot) -- dot pattern constraints
                          -- after elaboration, we check that the equations
                          -- are already solved, which shows that the term
                          -- in the pattern is valid by unification

{- Note on when holes must be resolved:
   - in a LHS, there must be no constraints generated or holes left over,
     not even named holes
   - anywhere else, if there are named holes, holes and constraints are
     fine, but they must be resolved by the end of the current block
     (meaning: pattern matching definition or data definition)
-}

export
initUState : UnifyState annot
initUState = MkUnifyState 0 [] [] [] empty []

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
         pure (n `elem` map snd (holes ust))

export
getHoleNames : {auto u : Ref UST (UState annot)} ->
               Core annot (List Name)
getHoleNames 
    = do ust <- get UST
         pure (map snd (holes ust))

export
getHoleInfo : {auto u : Ref UST (UState annot)} ->
               Core annot (List (annot, Name))
getHoleInfo 
    = do ust <- get UST
         pure (holes ust)

export
getCurrentHoleNames : {auto u : Ref UST (UState annot)} ->
                      Core annot (List Name)
getCurrentHoleNames 
    = do ust <- get UST
         pure (currentHoles ust)

export
getDelayedHoleNames : {auto u : Ref UST (UState annot)} ->
                   Core annot (List Name)
getDelayedHoleNames 
    = do ust <- get UST
         pure (delayedHoles ust)

export
resetHoles : {auto u : Ref UST (UState annot)} ->
             Core annot ()
resetHoles 
    = do ust <- get UST
         -- TODO: Also clear out solved/ImpBind holes
         put UST (record { currentHoles = [] } ust)

export
addHoleName : {auto u : Ref UST (UState annot)} ->
              annot -> Name -> Core annot ()
addHoleName loc n
    = do ust <- get UST
         put UST (record { holes $= ((loc, n) ::),
                           currentHoles $= (n ::) } ust)

-- Note that the given hole name arises from a type declaration, so needs
-- to be resolved later
export
addDelayedHoleName : {auto u : Ref UST (UState annot)} ->
                  Name -> Core annot ()
addDelayedHoleName n
    = do ust <- get UST
         put UST (record { delayedHoles $= (n ::) } ust)

dropFirst : (a -> b -> Bool) -> a -> List b -> List b
dropFirst f x [] = []
dropFirst f x (y :: ys) = if f x y then ys else y :: dropFirst f x ys

export
removeHoleName : {auto u : Ref UST (UState annot)} ->
                 Name -> Core annot ()
removeHoleName n
    = do ust <- get UST
         put UST (record { holes $= dropFirst (\x, y => x == snd y) n,
                           currentHoles $= dropFirst (==) n,
                           delayedHoles $= dropFirst (==) n } ust)

export
checkUserHoles : {auto u : Ref UST (UState annot)} ->
                 annot -> Bool -> Core annot ()
checkUserHoles loc now
    = do hs <- getCurrentHoleNames
         let hs' = if any isUserName hs then [] else hs
         when (not (isNil hs') && now) $ throw (UnsolvedHoles loc hs)
         -- Note the hole names, to ensure they are resolved
         -- by the end of elaborating the current source file
         hs <- getCurrentHoleNames
         traverse addDelayedHoleName hs
         pure ()

-- Make a new constant by applying a term to everything in the current
-- environment
mkConstant : Env Term vars -> Term vars -> ClosedTerm
mkConstant [] tm = tm
mkConstant {vars = x :: _} (b :: env) tm 
    = let ty = binderType b in
          mkConstant env (Bind x (Lam (multiplicity b) Explicit ty) tm)

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

export
applyTo : Term vars -> Env Term vars -> Term vars
applyTo {vars} tm env
  = let args = reverse (mkConstantAppArgs {done = []} env []) in
        apply tm (rewrite sym (appendNilRightNeutral vars) in args)

-- Apply a named constant to the current environment.
export
mkConstantApp : Name -> Env Term vars -> Term vars
-- Leftmost argument is the outermost variable, so make a list of local
-- variables then reverse it
mkConstantApp cn env = applyTo (Ref Func cn) env

-- Given a term and a type, add a new guarded constant to the global context
-- by applying the term to the current environment
-- Return its name
export
addConstant : {auto u : Ref UST (UState annot)} ->
              {auto c : Ref Ctxt Defs} ->
              annot -> Env Term vars -> 
              (tm : Term vars) -> (ty : Term vars) ->
              (constrs : List Name) ->
              Core annot Name
addConstant loc env tm ty constrs
    = do let def = mkConstant env tm
         let defty = mkConstantTy env ty
         let guess = newDef defty Public (Guess def constrs)
         cn <- genName "p"
         addHoleName loc cn
         addDef cn guess
         pure cn

-- Given a type and a name, add a new global metavariable
export
addNamedHole : {auto u : Ref UST (UState annot)} ->
               {auto c : Ref Ctxt Defs} ->
               annot -> Name -> (patvar : Bool) -> Env Term vars ->
               (ty : Term vars) -> Core annot ()
addNamedHole loc cn patvar env ty
    = do let defty = mkConstantTy env ty
         let hole = newDef defty Public (Hole (length env) patvar)
         addHoleName loc cn
         addDef cn hole

-- Given a type, add a new global metavariable and return its name
export
addHole : {auto u : Ref UST (UState annot)} ->
          {auto c : Ref Ctxt Defs} ->       
          annot -> Env Term vars ->
          (ty : Term vars) -> Core annot Name
addHole loc env ty
    = do cn <- genName "h"
         addNamedHole loc cn False env ty
         pure cn

-- Given a type, add a new global name for proof search to resolve, 
-- and return its name
export
addSearchable : {auto u : Ref UST (UState annot)} ->
                {auto c : Ref Ctxt Defs} ->       
                annot -> Env Term vars ->
                (ty : Term vars) -> Nat -> Core annot Name
addSearchable loc env ty depth
    = do cn <- genName "h"
         let defty = mkConstantTy env ty
         let hole = newDef defty Public (BySearch depth)
         addHoleName loc cn
         addDef cn hole
         pure cn

export
addBoundName : {auto u : Ref UST (UState annot)} ->
               {auto c : Ref Ctxt Defs} ->
               annot -> Name -> (patvar : Bool) -> Env Term vars ->
               (ty : Term vars) -> Core annot (Term vars)
addBoundName loc n patvar env exp
    = do addNamedHole loc n patvar env exp
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
         cn <- inCurrentNS (MN "constraint" c_id)
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
                    Just (BySearch _, ty) =>
                         log lvl $ "Search " ++ show hole ++ " : " ++ 
                                           show (normaliseHoles gam [] ty)
                    Just (PMDef _ args t, ty) =>
                         log 4 $ "Solved: " ++ show hole ++ " : " ++ 
                                       show (normalise gam [] ty) ++
                                       " = " ++ show (normalise gam [] (Ref Func hole))
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

-- Remove any solved hole names from the list; the assumption is that all
-- references to them have been removed with 'normaliseHoles' or by binding
-- as pattern/pi bound arguments.
-- It doesn't remove them from the context - but they won't get saved out as
-- .tti, and they may be overwritten with new definitions.
export
clearSolvedHoles : {auto u : Ref UST (UState annot)} -> 
                   {auto c : Ref Ctxt Defs} ->
                   Core annot ()
clearSolvedHoles
    = do hs <- getHoleNames
         gam <- getCtxt
         traverse (clearSolved gam) hs
         pure ()
  where
    clearSolved : Gamma -> Name -> Core annot ()
    clearSolved gam n
        = case lookupDefExact n gam of
               Just ImpBind => removeHoleName n
               Just (PMDef _ _ _) => removeHoleName n
               _ => pure ()

-- Make sure the types of holes have the references to solved holes normalised
-- away (since solved holes don't get written to .tti)
export
normaliseHoleTypes : {auto u : Ref UST (UState annot)} -> 
                     {auto c : Ref Ctxt Defs} ->
                     Core annot ()
normaliseHoleTypes
    = do hs <- getHoleNames
         gam <- getCtxt
         traverse (normaliseH gam) hs
         pure ()
  where
    updateType : Gamma -> Name -> GlobalDef -> Core annot ()
    updateType gam n def
        = do let ty' = normaliseHoles gam [] (type def)
             addDef n (record { type = ty' } def)

    normaliseH : Gamma -> Name -> Core annot ()
    normaliseH gam n
        = case lookupGlobalExact n gam of
               Just gdef =>
                  case definition gdef of
                       PMDef h _ _ => if h then updateType gam n gdef
                                           else pure ()
                       Hole _ _ => updateType gam n gdef
                       Guess _ _ => updateType gam n gdef
                       _ => pure ()
               Nothing => pure ()



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

