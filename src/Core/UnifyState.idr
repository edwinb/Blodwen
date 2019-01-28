module Core.UnifyState

import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT
import Core.TTC
import Utils.Binary

import Data.CSet
import Data.List
import Data.List.Views

import CompilerRuntime

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
     holes : List (annot, Name, Bool)
            -- unsolved metavariables in gamma (holes and guarded constants)
            -- along with where they were introduced,
            -- also whether they can be retried (i.e. they include constraints
            -- or search data)
     currentHoles : List (annot, Name) -- unsolved metavariables in this session
     delayedHoles : List (annot, Name)
                              -- unsolved metavariables which must be resolved 
                              -- but not necessarily in
                              -- the current session (any time later in the
                              -- source file is okay)
     constraints : Context (Constraint annot) -- metavariable constraints 
     dotConstraints : List (Name, String, Constraint annot) -- dot pattern constraints
                          -- after elaboration, we check that the equations
                          -- are already solved, which shows that the term
                          -- in the pattern is valid by unification. The Name
                          -- is the metavariable standing for the dot pattern,
                          -- which must be solved at the end
     delayedElab : Context (Core annot ClosedTerm)
                   -- Elaborators which we need to try again later, because
                   -- we didn't have enough type information to elaborate
                   -- successfully yet

{- Note on when holes must be resolved:
   - in a LHS, there must be no constraints generated or holes left over,
     not even named holes
   - anywhere else, if there are named holes, holes and constraints are
     fine, but they must be resolved by the end of the current block
     (meaning: pattern matching definition or data definition)
-}

export
initUState : UnifyState annot
initUState = MkUnifyState 0 [] [] [] empty [] empty

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
         pure (n `elem` map (Basics.fst . snd) (holes ust))

export
isCurrentHole : {auto u : Ref UST (UState annot)} ->
         Name -> Core annot Bool
isCurrentHole n 
    = do ust <- get UST
         pure (n `elem` map snd (currentHoles ust))

export
getHoleNames : {auto u : Ref UST (UState annot)} ->
               Core annot (List Name)
getHoleNames 
    = do ust <- get UST
         pure (map (Basics.fst . snd) (holes ust))

export
getHoleInfo : {auto u : Ref UST (UState annot)} ->
               Core annot (List (annot, Name, Bool))
getHoleInfo 
    = do ust <- get UST
         pure (holes ust)

export
getCurrentHoleNames : {auto u : Ref UST (UState annot)} ->
                      Core annot (List Name)
getCurrentHoleNames 
    = do ust <- get UST
         pure (map snd (currentHoles ust))

export
getCurrentHoleInfo : {auto u : Ref UST (UState annot)} ->
                     Core annot (List (annot, Name))
getCurrentHoleInfo
    = do ust <- get UST
         pure (currentHoles ust)

export
getDelayedHoleInfo : {auto u : Ref UST (UState annot)} ->
                   Core annot (List (annot, Name))
getDelayedHoleInfo 
    = do ust <- get UST
         pure (delayedHoles ust)

export
saveHoles : {auto u : Ref UST (UState annot)} ->
             Core annot (List (annot, Name))
saveHoles 
    = do ust <- get UST
         put UST (record { currentHoles = [] } ust)
         pure (currentHoles ust)

export
restoreHoles : {auto u : Ref UST (UState annot)} ->
               List (annot, Name) -> Core annot ()
restoreHoles hs
    = do ust <- get UST
         put UST (record { currentHoles = hs } ust)

export
addHoleName : {auto u : Ref UST (UState annot)} ->
              annot -> Name -> Bool -> Core annot ()
addHoleName loc n retry
    = do ust <- get UST
         put UST (record { holes $= ((loc, n, retry) ::),
                           currentHoles $= ((loc, n) ::) } ust)

-- Note that the given hole name arises from a type declaration, so needs
-- to be resolved later
export
addDelayedHoleName : {auto u : Ref UST (UState annot)} ->
                     annot -> Name -> Core annot ()
addDelayedHoleName loc n
    = do ust <- get UST
         put UST (record { delayedHoles $= ((loc, n) ::) } ust)

dropFirst : (a -> b -> Bool) -> a -> List b -> List b
dropFirst f x [] = []
dropFirst f x (y :: ys) = if f x y then dropFirst f x ys else y :: dropFirst f x ys

export
removeHoleName : {auto u : Ref UST (UState annot)} ->
                 Name -> Core annot ()
removeHoleName n
    = do ust <- get UST
         put UST (record { holes $= dropFirst (\x, y => x == fst (snd y)) n,
                           currentHoles $= dropFirst (\x, y => x == snd y) n,
                           delayedHoles $= dropFirst (\x, y => x == snd y) n } 
                  ust)

-- A hole is 'valid' - i.e. okay to leave unsolved for later - as long as it's
-- not guarded by a unification problem (in which case, report that the unification
-- problem is unsolved) and it doesn't depend on an implicit pattern variable
-- (in which case, perhaps suggest binding it explicitly)
export
checkValidHole : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST (UState annot)} ->
                 (annot, Name) -> Core annot ()
checkValidHole (loc, hole)
    = do gam <- get Ctxt
         ust <- get UST
         case lookupDefTyExact hole (gamma gam) of
              Nothing => pure ()
              Just (Guess tm (c :: _), ty) =>
                  case lookupCtxtExact c (constraints ust) of
                       Just (MkConstraint loc env x y) =>
                            throw (CantSolveEq loc env x y)
                       Just (MkSeqConstraint loc env (x :: xs) (y :: ys)) =>
                            throw (CantSolveEq loc env x y)
                       _ => pure ()
              Just (_, ty) => 
                  do traverse checkRef (toList (getRefs ty))
                     pure ()
              _ => pure ()
  where
    checkRef : Name -> Core annot ()
    checkRef (PV n f)
        = throw (GenericMsg loc ("Hole cannot depend on an unbound implicit " ++
                                 show n))
    checkRef _ = pure ()

-- Bool flag says whether it's an error for there to have been holes left
-- in the last session. Usually we can leave them to the end, but it's not
-- valid for there to be holes remaining when checking a LHS.
-- Also throw an error if there are unresolved guarded constants
export
checkUserHoles : {auto u : Ref UST (UState annot)} ->
                 {auto c : Ref Ctxt Defs} ->
                 Bool -> Core annot ()
checkUserHoles now
    = do hs <- getCurrentHoleInfo
         traverse checkValidHole hs
         let hs' = if any isUserName (map snd hs) then [] else hs
         when (not (isNil hs') && now) $ throw (UnsolvedHoles (nubBy sndEq hs))
         -- Note the hole names, to ensure they are resolved
         -- by the end of elaborating the current source file
         traverse (\x => addDelayedHoleName (fst x) (snd x)) hs'
         pure ()
  where
    sndEq : (a, Name) -> (a, Name) -> Bool
    sndEq x y = snd x == snd y

export
checkDelayedHoles : {auto u : Ref UST (UState annot)} ->
                    {auto c : Ref Ctxt Defs} ->
                    Core annot (Maybe (Error annot))
checkDelayedHoles
    = do hs <- getDelayedHoleInfo
         allHs <- getHoleNames
         if (not (isNil hs)) 
            then pure (Just (UnsolvedHoles (nubBy sndEq hs)))
            else pure Nothing
  where
    sndEq : (a, Name) -> (a, Name) -> Bool
    sndEq x y = snd x == snd y


-- Check that the argument types in a type are valid. If the unbound
-- implicit rules bind a thing too late (they bind dependencies at the point 
-- the name is first encountered) then further unification might require that
-- the name is used earlier in a type. If this happens, report that we
-- can't infer the argument type.
export
checkArgTypes : {auto c : Ref Ctxt Defs} ->
                annot -> Env Term vars -> Term vars -> Core annot ()
checkArgTypes loc env (Bind n (Pi c p ty) sc)
    = do let ns = toList (getRefs ty)
         defs <- get Ctxt
         traverse (checkDefinedName defs) ns
         checkArgTypes loc (Pi c p ty :: env) sc
  where
    badarg : Name -> Core annot ()
    badarg h = throw (CantInferArgType loc env n h ty)

    checkDefinedName : Defs -> Name -> Core annot ()
    checkDefinedName defs h
        = case lookupDefExact h (gamma defs) of
               Just ImpBind => badarg h
               _ => pure ()
checkArgTypes loc env tm = pure ()

-- Make a new constant by applying a term to everything in the current
-- environment (except the lets, which aren't in the constant's type)
mkConstant : Env Term vars -> Term vars -> ClosedTerm
mkConstant [] tm = tm
mkConstant (Let c val ty :: env) tm
    = mkConstant env (subst val tm)
mkConstant {vars = x :: _} (b :: env) tm 
    = let ty = binderType b in
          mkConstant env (Bind x (Lam (multiplicity b) Explicit ty) tm)

-- Make the type of a new constant which applies a term to everything in
-- the current environment
-- Use 'Nothing' as the multiplicity for the local, because we don't know
-- the context this is being checked in, which is important as well as the
-- binder. We only need to know the count for explicitly given variables 
-- anyway...
mkConstantTy : Env Term vars -> Term vars -> ClosedTerm
mkConstantTy = abstractEnvType 

mkConstantAppArgs : Bool -> Env Term vars -> 
                    List (Term done) -> List (Term (vars ++ done))
mkConstantAppArgs lets [] xs = xs
mkConstantAppArgs lets (Let c val ty :: env) xs
    = if lets
         then Local Nothing Here :: map weaken (mkConstantAppArgs lets env xs)
         else map weaken (mkConstantAppArgs lets env xs)
mkConstantAppArgs lets (b :: env) xs 
    = let rec = mkConstantAppArgs lets env xs in
          Local Nothing Here :: map weaken rec

export
applyTo : Term vars -> Env Term vars -> Term vars
applyTo {vars} tm env
  = let args = reverse (mkConstantAppArgs {done = []} False env []) in
        apply tm (rewrite sym (appendNilRightNeutral vars) in args)

export
applyToFull : Term vars -> Env Term vars -> Term vars
applyToFull {vars} tm env
  = let args = reverse (mkConstantAppArgs {done = []} True env []) in
        apply tm (rewrite sym (appendNilRightNeutral vars) in args)

mkConstantAppArgsSub : Bool -> Env Term vars -> SubVars smaller vars ->
                       List (Term done) -> List (Term (vars ++ done))
mkConstantAppArgsSub lets [] p xs = xs
mkConstantAppArgsSub lets (b :: env) SubRefl xs
    = let rec = mkConstantAppArgsSub lets env SubRefl xs in
          if lets 
             then Local Nothing Here :: map weaken rec
             else case b of
                     Let _ _ _ => map weaken rec
                     _ => Local Nothing Here :: map weaken rec
mkConstantAppArgsSub lets (b :: env) (DropCons p) xs
    = map weaken (mkConstantAppArgsSub lets env p xs)
mkConstantAppArgsSub lets (b :: env) (KeepCons p) xs
    = let rec = mkConstantAppArgsSub lets env p xs in
          if lets 
             then Local Nothing Here :: map weaken rec
             else case b of
                     Let _ _ _ => map weaken rec
                     _ => Local Nothing Here :: map weaken rec

export
applyToSub : Term vars -> Env Term vars -> SubVars smaller vars -> Term vars
applyToSub {vars} tm env sub
  = let args = reverse (mkConstantAppArgsSub {done = []} False env sub []) in
        apply tm (rewrite sym (appendNilRightNeutral vars) in args)

export
applyToSubFull : Term vars -> Env Term vars -> SubVars smaller vars -> Term vars
applyToSubFull {vars} tm env sub
  = let args = reverse (mkConstantAppArgsSub {done = []} True env sub []) in
        apply tm (rewrite sym (appendNilRightNeutral vars) in args)

mkConstantAppArgsOthers : Bool -> Env Term vars -> SubVars smaller vars ->
                       List (Term done) -> List (Term (vars ++ done))
mkConstantAppArgsOthers lets [] p xs = xs
mkConstantAppArgsOthers lets (b :: env) SubRefl xs
    = map weaken (mkConstantAppArgsOthers lets env SubRefl xs)
mkConstantAppArgsOthers lets (b :: env) (KeepCons p) xs
    = map weaken (mkConstantAppArgsOthers lets env p xs)
mkConstantAppArgsOthers lets (b :: env) (DropCons p) xs
    = let rec = mkConstantAppArgsOthers lets env p xs in
          if lets 
             then Local Nothing Here :: map weaken rec
             else case b of
                     Let _ _ _ => map weaken rec
                     _ => Local Nothing Here :: map weaken rec

export
applyToOthers : Term vars -> Env Term vars -> SubVars smaller vars -> Term vars
applyToOthers {vars} tm env sub
  = let args = reverse (mkConstantAppArgsOthers {done = []} False env sub []) in
        apply tm (rewrite sym (appendNilRightNeutral vars) in args)

export
applyToOthersFull : Term vars -> Env Term vars -> SubVars smaller vars -> Term vars
applyToOthersFull {vars} tm env sub
  = let args = reverse (mkConstantAppArgsOthers {done = []} True env sub []) in
        apply tm (rewrite sym (appendNilRightNeutral vars) in args)

-- Apply a named constant to the current environment, excluding lets.
export
mkConstantApp : Name -> Env Term vars -> Term vars
-- Leftmost argument is the outermost variable, so make a list of local
-- variables then reverse it
mkConstantApp cn env = applyTo (Ref Func cn) env

-- Apply a named constant to the current environment, including lets.
export
mkConstantAppFull : Name -> Env Term vars -> Term vars
-- Leftmost argument is the outermost variable, so make a list of local
-- variables then reverse it
mkConstantAppFull cn env = applyToFull (Ref Func cn) env

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
         let guess = newDef [] defty Public (Guess def constrs)
         cn <- genName "p"
         addHoleName loc cn True
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
         let hole = newDef [] defty Public (Hole (length env) patvar False)
         addHoleName loc cn False
         addDef cn hole

-- Given a type, add a new global metavariable and return its name
export
addHole : {auto u : Ref UST (UState annot)} ->
          {auto c : Ref Ctxt Defs} ->       
          annot -> Env Term vars -> 
          (ty : Term vars) -> String -> Core annot Name
addHole loc env ty base
    = do cn <- genName base
         addNamedHole loc cn False env ty
         pure cn

-- Given a type, add a new global name for proof search to resolve, 
-- and return its name
export
addSearchable : {auto u : Ref UST (UState annot)} ->
                {auto c : Ref Ctxt Defs} ->       
                annot -> Env Term vars ->
                (ty : Term vars) -> Nat -> Name -> Core annot Name
addSearchable loc env ty depth def
    = do cn <- genName "search"
         let defty = mkConstantTy env ty
         let hole = newDef [] defty Public (BySearch depth def)
         addHoleName loc cn True
         addDef cn hole
         pure cn

-- Add a hole which stands for a delayed elaborator, and return the
-- name of the hole while stands for it and a reference for the delayed
-- elaborator in the unification state
export
addDelayedElab : {auto u : Ref UST (UState annot)} ->
                 {auto c : Ref Ctxt Defs} ->       
                 annot -> Env Term vars ->
                 (ty : Term vars) -> Core annot (Name, ClosedTerm)
addDelayedElab loc env ty
    = do cn <- genName "delayed"
         let defty = mkConstantTy env ty
         let hole = newDef [] defty Public Delayed
         addHoleName loc cn False
         addDef cn hole
         pure (cn, defty)

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
         annot -> Env Term vars -> Name -> Term vars -> String -> Term vars ->
         Core annot ()
addDot loc env dotarg x reason y
    = do ust <- get UST
         put UST (record { dotConstraints $= ((dotarg, reason, MkConstraint loc env x y) ::) }
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
               gam <- get Ctxt
               case lookupDefTyExact hole (gamma gam) of
                    Nothing => pure ()
                    Just (Guess tm constraints, ty) => 
                         do log lvl $ "!" ++ show hole ++ " : " ++ 
                                              show (normaliseHoles gam [] ty)
                            log lvl $ "\t  = " ++ show (normaliseHoles gam [] tm)
                                            ++ "\n\twhen"
                            traverse (\x => dumpConstraint x) constraints 
                            pure ()
                    Just (Hole _ _ inj, ty) =>
                         log lvl $ "?" ++ show hole ++ " : " ++ 
                                           show (normaliseHoles gam [] ty)
                                           ++ if inj then " (Invertible)" else ""
                    Just (BySearch _ _, ty) =>
                         log lvl $ "Search " ++ show hole ++ " : " ++ 
                                           show (normaliseHoles gam [] ty)
                    Just (PMDef _ args t _ _, ty) =>
                         log 4 $ "Solved: " ++ show hole ++ " : " ++ 
                                       show (normalise gam [] ty) ++
                                       " = " ++ show (normalise gam [] (Ref Func hole))
                    Just (ImpBind, ty) =>
                         log 4 $ "Bound: " ++ show hole ++ " : " ++ 
                                       show (normalise gam [] ty)
                    Just (Delayed, ty) =>
                         log 4 $ "Delayed elaborator : " ++ 
                                       show (normalise gam [] ty)
                    _ => pure ()
  where
    dumpConstraint : Name -> Core annot ()
    dumpConstraint n
        = do ust <- get UST
             gam <- get Ctxt
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
    = do ust <- get UST
         if logLevel ust >= loglevel then
            do hs <- if all then getHoleNames else getCurrentHoleNames
               case hs of
                    [] => pure ()
                    _ => do log loglevel "--- CONSTRAINTS AND HOLES ---"
                            traverse (dumpHole loglevel) hs
                            pure ()
            else pure ()

-- Remove any solved hole names from the list; the assumption is that all
-- references to them have been removed with 'normaliseHoles' or by binding
-- as pattern/pi bound arguments.
-- It doesn't remove them from the context - but they won't get saved out as
-- .ttc, and they may be overwritten with new definitions.
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
               Just ImpBind 
                    => do log 5 $ "Removed bound hole " ++ show n
                          removeHoleName n
               Just (PMDef _ _ _ _ _) 
                    => do log 5 $ "Removed defined hole " ++ show n
                          removeHoleName n
               _ => pure ()

-- Make sure the types of holes have the references to solved holes normalised
-- away (since solved holes don't get written to .tti)
export
normaliseHoleTypes : {auto u : Ref UST (UState annot)} -> 
                     {auto c : Ref Ctxt Defs} ->
                     Core annot ()
normaliseHoleTypes
    = do hs <- getHoleNames
         ds <- get Ctxt
         traverse (normaliseH ds) hs
         pure ()
  where
    updateType : Defs -> Name -> GlobalDef -> Core annot ()
    updateType ds n def
        = do let ty' = normaliseHoles ds [] (type def)
             addDef n (record { type = ty' } def)

    normaliseH : Defs -> Name -> Core annot ()
    normaliseH ds n
        = case lookupGlobalExact n (gamma ds) of
               Just gdef =>
                  case definition gdef of
                       PMDef h _ _ _ _ 
                            => if h then updateType ds n gdef
                                    else pure ()
                       Hole _ _ _ => updateType ds n gdef
                       Guess _ _ => updateType ds n gdef
                       _ => pure ()
               Nothing => pure ()



export
dumpDots : {auto u : Ref UST (UState annot)} ->
           {auto c : Ref Ctxt Defs} ->
           Core annot ()
dumpDots
    = do ust <- get UST
         log 2 "--- DOT PATTERN CONSTRAINTS ---"
         gam <- get Ctxt
         traverse (dumpConstraint gam) (dotConstraints ust)
         pure ()
  where
    dumpConstraint : Defs -> (Name, String, Constraint annot) -> Core annot ()
    dumpConstraint gam (n, reason, MkConstraint _ env x y)
        = do log 2 $ "\t (" ++ show n ++ ", " ++ reason ++ ") " ++ show (normalise gam env x) 
                            ++ " =?= " ++ show (normalise gam env y)
             log 5 $ "\t    from " ++ show x 
                            ++ " =?= " ++ show y
    dumpConstraint gam _ = pure ()

