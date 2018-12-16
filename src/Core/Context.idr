module Core.Context

import Core.CaseTree
import Core.CompileExpr
import public Core.Core
import public Core.Hash
import Core.TT
import Core.TTC
import Core.Options

import Utils.Binary

import public Control.Catchable

import Data.CMap
import Data.StringMap
import Data.CSet
import Data.List

%default total

public export
record Context a where
     constructor MkContext 
     -- for looking up by exact (completely qualified) names
     exactNames : SortedMap a 
     -- for looking up hole and pattern names
     holeNames : SortedMap a
     -- for looking up by name root or partially qualified (so possibly
     -- ambiguous) names. This doesn't store machine generated names.
     hierarchy : StringMap (List (Name, a))
     -- Namespaces which are visible (i.e. have been imported)
     -- This only matters during evaluation and type checking, to control
     -- access in a program - in all other cases, we'll assume everything is
     -- visible
     visibleNS : List (List String)

export
empty : Context a
empty = MkContext empty empty empty []

export
lookupCtxtExact : Name -> Context a -> Maybe a
lookupCtxtExact n@(NS _ (MN _ _)) dict 
    = case lookup n (holeNames dict) of
           Nothing => lookup n (exactNames dict)
           Just res => Just res
lookupCtxtExact n@(PV _ _) dict
    = case lookup n (holeNames dict) of
           Nothing => lookup n (exactNames dict)
           Just res => Just res
lookupCtxtExact n dict = lookup n (exactNames dict)

export
lookupCtxtName : Name -> Context a -> List (Name, a)
lookupCtxtName n dict
    = case userNameRoot n of
           Nothing => case lookupCtxtExact n dict of
                           Nothing => []
                           Just res => [(n, res)]
           Just r => case lookup r (hierarchy dict) of
                          Nothing => []
                          Just ns => filter (matches n) ns
	where
		-- Name matches if a prefix of the namespace matches a prefix of the 
    -- namespace in the context
    matches : Name -> (Name, a) -> Bool
    matches (NS ns _) (NS cns _, _) = ns `isPrefixOf` cns
    matches (NS _ _) _ = True -- no in library name, so root doesn't match
    matches _ _ = True -- no prefix, so root must match, so good

export
lookupCtxt : Name -> Context a -> List a
lookupCtxt n dict = map snd (lookupCtxtName n dict)

addToHier : Name -> a -> 
						StringMap (List (Name, a)) -> StringMap (List (Name, a))
addToHier n val hier
     -- Only add user defined names. Machine generated names can only be
		 -- found with the exactNames
     = case userNameRoot n of
            Nothing => hier
            Just root =>
                 case lookup root hier of
                      Nothing => insert root [(n, val)] hier
                      Just ns => insert root (update val ns) hier
  where
    update : a -> List (Name, a) -> List (Name, a)
    update val [] = [(n, val)]
    update val (old :: xs) 
		    = if n == fst old 
					   then (n, val) :: xs
						 else old :: update val xs

export
addCtxt : Name -> a -> Context a -> Context a
addCtxt n@(PV _ _) val (MkContext dict holes hier vis)
     = let holes' = insert n val holes in
           MkContext dict holes' hier vis
addCtxt n@(NS _ (MN _ _)) val (MkContext dict holes hier vis)
     = let holes' = insert n val holes in
           MkContext dict holes' hier vis
addCtxt n val (MkContext dict holes hier vis) 
     = let dict' = insert n val dict
           hier' = addToHier n val hier in
           MkContext dict' holes hier' vis

-- Only deletes from hole name lookups, so only used for hole/pattern var
-- names
export
deleteCtxt : Name -> Context a -> Context a
deleteCtxt n (MkContext dict holes hier vis)
    = let holes' = delete n holes in
          MkContext dict holes' hier vis

export
deleteCtxtNames : List Name -> Context a -> Context a
deleteCtxtNames ns (MkContext dict holes hier vis)
    = let holes' = deleteNs ns holes in
          MkContext dict holes' hier vis
  where
    deleteNs : List Name -> SortedMap a -> SortedMap a
    deleteNs [] d = d
    deleteNs (n :: ns) d = deleteNs ns (delete n d)

-- Move the current set of holes to the exactNames list, since we probably
-- don't need quick access when the definition they arise from is done.
export
promoteHoles : Context a -> Context a
promoteHoles (MkContext dict holes hier vis)
    = let dict' = insertHoles (toList holes) dict in
          MkContext dict' empty hier vis
  where
    insertHoles : List (Name, a) -> SortedMap a -> SortedMap a
    insertHoles [] dict = dict
    insertHoles ((k, v) :: hs) dict = insertHoles hs (insert k v dict)

-- Merge two contexts, with entries in the second overriding entries in
-- the first
export
mergeContext : Context a -> Context a -> Context a
mergeContext ctxt (MkContext exact holes hier vis)
    = record { visibleNS $= (vis ++) } (insertFrom (toList exact ++ toList holes) ctxt)
  where
    insertFrom : List (Name, a) -> Context a -> Context a
    insertFrom [] ctxt = ctxt
    insertFrom ((n, val) :: cs) ctxt
        = insertFrom cs (addCtxt n val ctxt)

export
mergeContextAs : List String -> List String ->
                 Context a -> Context a -> Context a
mergeContextAs oldns newns ctxt (MkContext exact holes hier vis)
    = record { visibleNS $= (vis ++) } (insertFrom (toList exact ++ toList holes) ctxt)
  where
    insertFrom : List (Name, a) -> Context a -> Context a
    insertFrom [] ctxt = ctxt
    insertFrom ((n, val) :: cs) ctxt
        = insertFrom cs (addCtxt n val ctxt)

export
fromList : List (Name, a) -> Context a
fromList [] = empty
fromList ((n, val) :: rest) = addCtxt n val (fromList rest)

export
toList : Context a -> List (Name, a)
toList = toList . exactNames

export
TTC annot a => TTC annot (Context a) where
  toBuf b ctxt = toBuf b (toList (exactNames ctxt) ++ 
                          toList (holeNames ctxt))
  fromBuf s b
      = do xs <- fromBuf s b
           pure (fromList xs)

public export
data Def : Type where
     None  : Def -- Not yet defined
     PMDef : (ishole : Bool) -> (args : List Name) -> 
             (treeCT : CaseTree args) -> -- Compile time case tree
             (treeRT : CaseTree args) -> -- Run time case tree (0 multiplicities erased)
             (pats : List (List Name, ClosedTerm, ClosedTerm)) ->
                      -- original checked patterns (lhs/rhs) with the
                      -- names in the environment
                      -- Patterns are used for display purposes only, and will
                      -- only be there for definitions arising from the
                      -- TTImp elaborator
             Def
     ExternDef : (arity : Nat) -> Def
     Builtin : PrimFn arity -> Def
     DCon  : (tag : Int) -> (arity : Nat) -> 
						 (forcedpos : List Nat) -> -- argument positions whose value is
			                         -- forced by the constructors type
			       Def
     TCon  : (tag : Int) -> (arity : Nat) -> 
						 (parampos : List Nat) -> -- argument positions which are parametric
             (detpos : List Nat) -> -- argument postitions for determining auto search
						 (datacons : List Name) -> 
			       Def
     Hole : (numlocs : Nat) -> (pvar : Bool) -> (invertible : Bool) -> Def 
		           -- Unsolved hole, under 'numlocs' locals; whether it
						   -- is standing for a pattern variable (and therefore mustn't
							 -- be solved); whether we've established it's invertible
               -- via proof search (i.e. it's a parameter of a thing we're
               -- searching for, and it's invertible in all the possible hints)
               -- An application is invertible if you can get the arguments by
               -- looking at the result. e.g. constructors. trivially.
     BySearch : Nat -> Name -> Def 
                    -- Undefined name, to be defined by proof search. Stores
                    -- the maximum search depth, and the function it's being
                    -- used in (to prevent recursive search)
                    -- e.g. auto implicit or interface implementation
     ImpBind : Def -- Hole turned into an implicitly bound variable
                   -- (which will be deleted after elaboration)
     -- The constraint names refer into a context of constraints,
     -- defined in Core.UnifyState
     Guess : (guess : ClosedTerm) -> (constraints : List Name) -> Def
     -- A delayed elaboration. The elaborators themselves are stored in the
     -- unifiation state
     Delayed : Def

export
Show Def where
  show None = "No definition"
  show (PMDef hole args tree _ _) 
      = showHole hole ++"; " ++ show args ++ ";" ++ show tree
    where
      showHole : Bool -> String
      showHole h = if h then "Solved hole" else "Def"
  show (ExternDef arity)
      = "<<external definition with " ++ show arity ++ " arguments>>"
  show (Builtin {arity} f)
      = "<<builtin with " ++ show arity ++ " arguments>>"
  show (TCon tag arity params dets cons)
	    = "TyCon " ++ show tag ++ "; arity " ++ show arity ++ "; params " ++
        show params ++ "; determining " ++ show dets ++ 
        "; constructors " ++ show cons
  show (DCon tag arity forced)
      = "DataCon " ++ show tag ++ "; arity " ++ show arity ++ 
        "; forced positions " ++ show forced
  show (Hole locs False _)
      = "Hole with " ++ show locs ++ " locals"
  show (Hole locs True _)
      = "Pattern variable with " ++ show locs ++ " locals"
  show (BySearch n _)
      = "Search with depth " ++ show n
  show ImpBind = "Implicitly bound name"
  show (Guess g cons) = "Guess " ++ show g ++ " with constraints " ++ show cons
  show Delayed = "Delayed"

TTC annot Def where
  toBuf b None = tag 0
  toBuf b (PMDef ishole args ct rt pats) 
      = do tag 1; toBuf b ishole; toBuf b args; toBuf b ct; toBuf b rt
           toBuf b pats
  toBuf b (ExternDef arity)
      = do tag 2; toBuf b arity;
  toBuf b (Builtin _)
      = throw (InternalError "Trying to serialise a Builtin")
  toBuf b (DCon t arity forcedpos) 
      = do tag 3; toBuf b t; toBuf b arity; toBuf b forcedpos
  toBuf b (TCon t arity parampos detpos datacons) 
      = do tag 4; toBuf b t; toBuf b arity; toBuf b parampos; 
           toBuf b detpos; toBuf b datacons
  toBuf b (Hole numlocs pvar inv) 
      = do tag 5; toBuf b numlocs; toBuf b pvar; toBuf b inv
  toBuf b (BySearch k d) 
      = do tag 6; toBuf b k; toBuf b d
  toBuf b ImpBind = tag 7
  toBuf b (Guess guess constraints) 
      = do tag 8; toBuf b guess; toBuf b constraints
  toBuf b Delayed
      = throw (InternalError "Trying to serialise a Delayed elaborator")

  fromBuf s b 
      = case !getTag of
             0 => pure None
             1 => do w <- fromBuf s b; x <- fromBuf s b; y <- fromBuf s b; z <- fromBuf s b
                     p <- fromBuf s b
                     pure (PMDef w x y z p)
             2 => do a <- fromBuf s b
                     pure (ExternDef a)
             3 => do x <- fromBuf s b; y <- fromBuf s b; z <- fromBuf s b
                     pure (DCon x y z)
             4 => do v <- fromBuf s b; w <- fromBuf s b; x <- fromBuf s b; y <- fromBuf s b; z <- fromBuf s b
                     pure (TCon v w x y z)
             5 => do x <- fromBuf s b; y <- fromBuf s b; z <- fromBuf s b
                     pure (Hole x y z)
             6 => do x <- fromBuf s b; y <- fromBuf s b
                     pure (BySearch x y)
             7 => pure ImpBind
             8 => do x <- fromBuf s b; y <- fromBuf s b
                     pure (Guess x y)
             _ => corrupt "Def"

public export
data DefFlag 
    = TypeHint Name Bool -- True == direct hint
    | GlobalHint Bool -- True == always search (not a default hint)
    | Inline
    | Invertible -- assume safe to cancel arguments in unification
    | Overloadable -- allow ad-hoc overloads

export
Eq DefFlag where
    (==) (TypeHint ty x) (TypeHint ty' y) = ty == ty' && x == y
    (==) (GlobalHint x) (GlobalHint y) = x == y
    (==) Inline Inline = True
    (==) Invertible Invertible = True
    (==) Overloadable Overloadable = True
    (==) _ _ = False

TTC annot DefFlag where
  toBuf b (TypeHint x y) = do tag 0; toBuf b x; toBuf b y
  toBuf b (GlobalHint t) = do tag 1; toBuf b t
  toBuf b Inline = tag 2
  toBuf b Invertible = tag 3
  toBuf b Overloadable = tag 4

  fromBuf s b 
      = case !getTag of
             0 => do x <- fromBuf s b; y <- fromBuf s b; pure (TypeHint x y)
             1 => do t <- fromBuf s b; pure (GlobalHint t)
             2 => pure Inline
             3 => pure Invertible
             4 => pure Overloadable
             _ => corrupt "DefFlag"

-- *everything* about a definition goes here, so that we can save out the
-- type checked code "simply" by writing out a list of GlobalDefs
public export
record GlobalDef where
     constructor MkGlobalDef
     type : ClosedTerm
     multiplicity : RigCount
     vars : List Name -- Environment name is defined in
     visibility : Visibility
     totality : Totality
     flags : List DefFlag
     definition : Def
     compexpr : Maybe CDef
     refersTo : List Name

TTC annot GlobalDef where
  toBuf b def
      = do toBuf b (type def)
           toBuf b (multiplicity def)
           toBuf b (vars def)
           toBuf b (visibility def)
           toBuf b (totality def)
           toBuf b (flags def)
           toBuf b (definition def)
           toBuf b (compexpr def)
           toBuf b (refersTo def)

  fromBuf s b
      = do ty <- fromBuf s b
           mult <- fromBuf s b
           vars <- fromBuf s b
           vis <- fromBuf s b
           tot <- fromBuf s b
           flgs <- fromBuf s b
           def <- fromBuf s b
           exp <- fromBuf s b
           ref <- fromBuf s b
           pure (MkGlobalDef ty mult vars vis tot flgs def exp ref)

getRefs : Def -> List Name
getRefs None = []
getRefs (PMDef ishole args sc _ _) = getRefs sc
getRefs (ExternDef _) = []
getRefs (Builtin _) = []
getRefs (DCon tag arity forced) = []
getRefs (TCon tag arity params dets datacons) = []
getRefs (Hole numlocs _ _) = []
getRefs (BySearch _ _) = []
getRefs ImpBind = []
getRefs (Guess guess constraints) = CSet.toList (getRefs guess)
getRefs Delayed = []

export
newRigDef : RigCount -> List Name -> 
            (ty : ClosedTerm) -> (vis : Visibility) -> Def -> GlobalDef
newRigDef r vars ty vis def 
   = MkGlobalDef ty r vars vis Unchecked [] def Nothing (getRefs def)

export
newDef : List Name -> (ty : ClosedTerm) -> (vis : Visibility) -> Def -> GlobalDef
newDef = newRigDef RigW

-- A context of global definitions
public export
Gamma : Type
Gamma = Context GlobalDef

-- Everything needed to typecheck data types/functions
public export
record Defs where
      constructor MkAllDefs
      gamma : Gamma -- All the definitions
      currentNS : List String -- namespace for current definitions
      options : Options
      toSave : SortedSet -- Definitions to write out as .tti
      imported : List (List String, Bool, List String) 
          -- imported modules, to rexport, as namespace
      importHashes : List (List String, Int)
          -- interface hashes of imported modules
      allImported : List (String, List String)
          -- all imported filenames/namespaces, just to avoid loading something
          -- twice unnecessarily (this is a record of all the things we've
          -- called 'readFromTTC' with, in practice)
      autoHints : List (Bool, Name) -- global auto hints.
                  -- boolean flag means whether to always run 'True' or just
                  -- at the end to resolve defaults 'False'
      typeHints : Context (List (Name, Bool)) -- type name hints
      openHints : List Name -- global hints just for this module; prioritised
      hiddenNames : List Name -- names which should be considered hidden (treated 'private')
      cgdirectives : List (CG, String)
      nextTag : Int -- next tag for type constructors
      nextHole : Int -- next hole/constraint id
      nextVar	: Int
      ifaceHash : Int

export
noGam : Defs -> Defs
noGam = record { gamma = empty }

-- Just write out what's in "gamma", the relevant options, and the imported
-- modules
-- Everything else is either reconstructed from that, or not used when reading
-- from a file
export
TTC annot Defs where
  toBuf b val 
      = do toBuf b (currentNS val)
           toBuf b (imported val)
           toBuf b (CMap.toList (exactNames (gamma val)))
           toBuf b (laziness (options val))
           toBuf b (pairnames (options val))
           toBuf b (rewritenames (options val))
           toBuf b (primnames (options val))
           toBuf b (namedirectives (options val))
           toBuf b (hiddenNames val)
           toBuf b (cgdirectives val)
  fromBuf s b
      = do modNS <- fromBuf s b
           imported <- fromBuf s b
           ns <- fromBuf s b {a = List (Name, GlobalDef)}
           lazy <- fromBuf s b
           pair <- fromBuf s b
           rw <- fromBuf s b
           prim <- fromBuf s b
           ndirs <- fromBuf s b
           hides <- fromBuf s b
           ds <- fromBuf s b
           pure (MkAllDefs (insertFrom ns empty) modNS 
                            (record { laziness = lazy,
                                      pairnames = pair,
                                      rewritenames = rw,
                                      primnames = prim,
                                      namedirectives = ndirs
                                    } defaults)
                            empty imported [] [] [] empty [] hides ds 100 0 0 5381)
    where
      insertFrom : List (Name, GlobalDef) -> Gamma -> Gamma
      insertFrom [] ctxt = ctxt
      insertFrom ((n, val) :: cs) ctxt
          = insertFrom cs (addCtxt n val ctxt)

export
initCtxt : Defs
initCtxt = MkAllDefs empty ["Main"] defaults empty [] [] [] [] empty [] [] [] 100 0 0 5381

export
getSave : Defs -> List Name
getSave = toList . toSave

export
lookupGlobalExact : Name -> Gamma -> Maybe GlobalDef
lookupGlobalExact n gam = lookupCtxtExact n gam

export
lookupGlobalName : Name -> Gamma -> List (Name, GlobalDef)
lookupGlobalName n gam = lookupCtxtName n gam
    
-- private names are only visible in this namespace if their namespace
-- is the current namespace (or an outer one)
-- that is: given that most recent namespace is first in the list,
-- the namespace of 'n' is a suffix of nspace
export
visibleIn : (nspace : List String) -> Name -> Visibility -> Bool
visibleIn nspace (NS ns n) Private = isSuffixOf ns nspace
-- Public and Export names are always visible
visibleIn nspace n _ = True

-- TODO: This also needs to take into account totality, later
export
reducibleIn : (nspace : List String) -> Name -> Visibility -> Bool
reducibleIn nspace (NS ns n) Export = isSuffixOf ns nspace
reducibleIn nspace (NS ns n) Private = isSuffixOf ns nspace
reducibleIn nspace n _ = True

export
lookupDefExact : Name -> Gamma -> Maybe Def
lookupDefExact n gam
    = do def <- lookupGlobalExact n gam
         pure (definition def)

export
lookupDefName : Name -> Gamma -> List (Name, Def)
lookupDefName n gam
    = map (\(x, g) => (x, definition g)) (lookupGlobalName n gam)

export
lookupTyExact : Name -> Gamma -> Maybe ClosedTerm
lookupTyExact n gam 
    = do def <- lookupGlobalExact n gam
         pure (type def)

export
lookupTyName : Name -> Gamma -> List (Name, ClosedTerm)
lookupTyName n gam
    = map (\(x, g) => (x, type g)) (lookupGlobalName n gam)

export
lookupDefTyExact : Name -> Gamma -> Maybe (Def, ClosedTerm)
lookupDefTyExact n gam 
    = do def <- lookupGlobalExact n gam
         pure (definition def, type def)

export
lookupDefTyName : Name -> Gamma -> List (Name, Def, ClosedTerm)
lookupDefTyName n gam
    = map (\(x, g) => (x, definition g, type g)) (lookupGlobalName n gam)

export
lookupGlobalNameIn : (nspace : List String) ->
                     Name -> Gamma -> List (Name, GlobalDef)
lookupGlobalNameIn nspace n gam
    = filter isVisible (lookupGlobalName n gam)
  where
    isVisible : (Name, GlobalDef) -> Bool
    isVisible (n, gdef) = visibleIn nspace n (visibility gdef)

export
lookupDefTyNameIn : (nspace : List String) ->
                    Name -> Gamma -> List (Name, Def, ClosedTerm)
lookupDefTyNameIn nspace n gam
    = map (\ (x, d, t, v) => (x, d, t)) $
        filter isVisible $
          map (\ (x, g) => (x, definition g, type g, visibility g)) 
            (lookupGlobalName n gam)
  where
    isVisible : (Name, Def, ClosedTerm, Visibility) -> Bool
    isVisible (n, d, t, v) = visibleIn nspace n v


public export
record Constructor where
  constructor MkCon
  name : Name
  arity : Nat
  type : ClosedTerm

public export
data DataDef : Type where
     MkData : (tycon : Constructor) -> (datacons : List Constructor) ->
              DataDef

public export
data Clause : Type where
     MkClause : (env : Env Term vars) ->
                (lhs : Term vars) -> (rhs : Term vars) -> Clause

public export
data FnDef : Type where
     MkFn : (n : Name) -> (ty : ClosedTerm) -> (clauses : List Clause) ->
            FnDef

-- A label for the context in the global state
export
data Ctxt : Type where

export
getCtxt : {auto c : Ref Ctxt Defs} ->
					Core annot Gamma
getCtxt = pure (gamma !(get Ctxt))

-- Reset the context, except for the options
export
clearCtxt : {auto c : Ref Ctxt Defs} ->
            Core annot ()
clearCtxt
    = do defs <- get Ctxt
         put Ctxt (record { options = options defs } initCtxt)

export
addHash : {auto c : Ref Ctxt Defs} ->
          Hashable a => a -> Core annot ()
addHash x
    = do defs <- get Ctxt
         put Ctxt (record { ifaceHash = hashWithSalt (ifaceHash defs) x } defs)

export
initHash : {auto c : Ref Ctxt Defs} -> Core annot ()
initHash
    = do defs <- get Ctxt
         put Ctxt (record { ifaceHash = 5381 } defs)

export
isDelayType : Name -> Defs -> Bool
isDelayType n defs
    = case laziness (options defs) of
           Nothing => False
           Just l => active l && n == delayType l

export
isDelay : Name -> Defs -> Bool
isDelay n defs
    = case laziness (options defs) of
           Nothing => False
           Just l => active l && n == delay l

export
isForce : Name -> Defs -> Bool
isForce n defs
    = case laziness (options defs) of
           Nothing => False
           Just l => active l && n == force l

export
delayName : Defs -> Maybe Name
delayName defs
    = do l <- laziness (options defs)
         if active l
            then pure (delay l)
            else Nothing

export
forceName : Defs -> Maybe Name
forceName defs
    = do l <- laziness (options defs)
         if active l
            then pure (force l)
            else Nothing

export
isPairType : Name -> Defs -> Bool
isPairType n defs
    = case pairnames (options defs) of
           Nothing => False
           Just l => n == pairType l

export
fstName : Defs -> Maybe Name
fstName defs
    = do l <- pairnames (options defs)
         pure (fstName l)

export
sndName : Defs -> Maybe Name
sndName defs
    = do l <- pairnames (options defs)
         pure (sndName l)

export
getRewrite : Defs -> Maybe Name
getRewrite defs
    = do r <- rewritenames (options defs)
         pure (rewriteName r)

export
isEqualTy : Name -> Defs -> Bool
isEqualTy n defs
    = case rewritenames (options defs) of
           Nothing => False
           Just r => n == equalType r

export
fromIntegerName : Defs -> Maybe Name
fromIntegerName defs
    = fromIntegerName (primnames (options defs))

export
fromStringName : Defs -> Maybe Name
fromStringName defs
    = fromStringName (primnames (options defs))

export
fromCharName : Defs -> Maybe Name
fromCharName defs
    = fromCharName (primnames (options defs))

export
setVisible : {auto c : Ref Ctxt Defs} -> 
             (nspace : List String) -> Core annot ()
setVisible nspace
    = do defs <- get Ctxt
         put Ctxt (record { gamma->visibleNS $= (nspace ::) } defs)

-- Return True if the given namespace is visible in the context (meaning
-- the namespace itself, and any namespace it's nested inside)
export
isVisible : {auto c : Ref Ctxt Defs} -> 
            (nspace : List String) -> Core annot Bool
isVisible nspace
    = do defs <- get Ctxt
         pure (any visible (allParents (currentNS defs) ++ visibleNS (gamma defs)))
  where
    allParents : List String -> List (List String)
    allParents [] = []
    allParents (n :: ns) = (n :: ns) :: allParents ns

    -- Visible if any visible namespace is a suffix of the namespace we're
    -- asking about
    visible : List String -> Bool
    visible visns = isSuffixOf visns nspace

export
checkUnambig : {auto c : Ref Ctxt Defs} ->
               annot -> Name -> Core annot Name
checkUnambig loc n
    = do defs <- get Ctxt
         case lookupDefName n (gamma defs) of
              [] => throw (UndefinedName loc n)
              [(fulln, _)] => pure fulln
              ns => throw (AmbiguousName loc (map fst ns))

export
setLazy : {auto c : Ref Ctxt Defs} ->
          annot -> (delayType : Name) -> (delay : Name) -> (force : Name) ->
          Core annot ()
setLazy loc ty d f
    = do defs <- get Ctxt
         ty' <- checkUnambig loc ty
         d' <- checkUnambig loc d
         f' <- checkUnambig loc f
         put Ctxt (record { options $= setLazy ty' d' f' } defs)

export
lazyActive : {auto c : Ref Ctxt Defs} ->
             Bool -> Core annot ()
lazyActive a
    = do defs <- get Ctxt
         let l = laziness (options defs)
         maybe (pure ())
               (\lns => 
                    do let l' = record { active = a } lns
                       put Ctxt (record { options->laziness = Just l' }
                                        defs)) l

export
isLazyActive : {auto c : Ref Ctxt Defs} ->
               Core annot Bool
isLazyActive
    = do defs <- get Ctxt
         pure (maybe False active (laziness (options defs)))

export
setPair : {auto c : Ref Ctxt Defs} ->
          annot -> (pairType : Name) -> (fstn : Name) -> (sndn : Name) ->
          Core annot ()
setPair loc ty f s
    = do defs <- get Ctxt
         ty' <- checkUnambig loc ty
         f' <- checkUnambig loc f
         s' <- checkUnambig loc s
         put Ctxt (record { options $= setPair ty' f' s' } defs)

export
setRewrite : {auto c : Ref Ctxt Defs} ->
             annot -> (eq : Name) -> (rwlemma : Name) -> Core annot ()
setRewrite loc eq rw
    = do defs <- get Ctxt
         rw' <- checkUnambig loc rw
         eq' <- checkUnambig loc eq
         put Ctxt (record { options $= setRewrite eq' rw' } defs)

-- Don't check for ambiguity here; they're all meant to be overloadable
export
setFromInteger : {auto c : Ref Ctxt Defs} ->
                 annot -> Name -> Core annot ()
setFromInteger loc n
    = do defs <- get Ctxt
         put Ctxt (record { options $= setFromInteger n } defs)

export
setFromString : {auto c : Ref Ctxt Defs} ->
                annot -> Name -> Core annot ()
setFromString loc n
    = do defs <- get Ctxt
         put Ctxt (record { options $= setFromString n } defs)

export
setFromChar : {auto c : Ref Ctxt Defs} ->
              annot -> Name -> Core annot ()
setFromChar loc n
    = do defs <- get Ctxt
         put Ctxt (record { options $= setFromChar n } defs)

export
addNameDirective : {auto c : Ref Ctxt Defs} ->
                   annot -> Name -> List String -> Core annot ()
addNameDirective loc n ns
    = do defs <- get Ctxt
         n' <- checkUnambig loc n
         put Ctxt (record { options $= addNameDirective (n', ns) } defs)

export
setPPrint : {auto c : Ref Ctxt Defs} ->
            PPrinter -> Core annot ()
setPPrint ppopts
    = do defs <- get Ctxt
         put Ctxt (record { options->printing = ppopts } defs)

export
getSession : {auto c : Ref Ctxt Defs} ->
             Core annot Session
getSession
    = do defs <- get Ctxt
         pure (session (options defs))

export
setSession : {auto c : Ref Ctxt Defs} ->
             Session -> Core annot ()
setSession sopts
    = do defs <- get Ctxt
         put Ctxt (record { options->session = sopts } defs)

export
setCG : {auto c : Ref Ctxt Defs} ->
        CG -> Core annot ()
setCG cg
    = do defs <- get Ctxt
         put Ctxt (record { options->session->codegen = cg } defs)

export
getPPrint : {auto c : Ref Ctxt Defs} ->
            Core annot PPrinter
getPPrint
    = do defs <- get Ctxt
         pure (printing (options defs))

export
getDirs : {auto c : Ref Ctxt Defs} -> Core annot Dirs
getDirs
    = do defs <- get Ctxt
         pure (dirs (options defs))

export
addExtraDir : {auto c : Ref Ctxt Defs} -> String -> Core annot ()
addExtraDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->extra_dirs $= (++ [dir]) } defs)

export
addDataDir : {auto c : Ref Ctxt Defs} -> String -> Core annot ()
addDataDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->data_dirs $= (++ [dir]) } defs)

export
setBuildDir : {auto c : Ref Ctxt Defs} -> String -> Core annot ()
setBuildDir dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->build_dir = dir } defs)

export
setWorkingDir : {auto c : Ref Ctxt Defs} -> String -> Core annot ()
setWorkingDir dir
    = do defs <- get Ctxt
         coreLift $ changeDir dir
         cdir <- coreLift $ currentDir
         put Ctxt (record { options->dirs->working_dir = cdir } defs)

export
setPrefix : {auto c : Ref Ctxt Defs} -> String -> Core annot ()
setPrefix dir
    = do defs <- get Ctxt
         put Ctxt (record { options->dirs->dir_prefix = dir } defs)

export
setExtension : {auto c : Ref Ctxt Defs} -> LangExt -> Core annot ()
setExtension e
    = do defs <- get Ctxt
         put Ctxt (record { options $= setExtension e } defs)

export
isExtension : LangExt -> Defs -> Bool
isExtension e defs = isExtension e (options defs)

-- Set the default namespace for new definitions
export
setNS : {auto c : Ref Ctxt Defs} ->
        List String -> Core annot ()
setNS ns
    = do defs <- get Ctxt
         put Ctxt (record { currentNS = ns } defs)

-- Get the default namespace for new definitions
export
getNS : {auto c : Ref Ctxt Defs} ->
        Core annot (List String)
getNS 
    = do defs <- get Ctxt
         pure (currentNS defs)

-- Add the module name, and namespace, of an imported module
-- (i.e. for "import X as Y", it's (X, Y)
-- "import public X" is, when rexported, the same as 
-- "import X as [current namespace]")
export
addImported : {auto c : Ref Ctxt Defs} ->
              (List String, Bool, List String) -> Core annot ()
addImported mod
    = do defs <- get Ctxt
         put Ctxt (record { imported $= (mod ::) } defs)

export
getImported : {auto c : Ref Ctxt Defs} -> 
              Core annot (List (List String, Bool, List String))
getImported
    = do defs <- get Ctxt
         pure (imported defs)

export
addDirective : {auto c : Ref Ctxt Defs} ->
               String -> String -> Core annot ()
addDirective c str
    = do defs <- get Ctxt
         case getCG c of
              Nothing => -- warn, rather than fail, because the CG may exist
                         -- but be unknown to this particular instance
                         coreLift $ putStrLn $ "Unknown code generator " ++ c
              Just cg => put Ctxt (record { cgdirectives $= ((cg, str) ::) } defs)

export
getDirectives : {auto c : Ref Ctxt Defs} ->
                CG -> Core annot (List String)
getDirectives cg
    = do defs <- get Ctxt
         pure (mapMaybe getDir (cgdirectives defs))
  where
    getDir : (CG, String) -> Maybe String
    getDir (x', str) = if cg == x' then Just str else Nothing


-- Add a new nested namespace to the current namespace for new definitions
-- e.g. extendNS ["Data"] when namespace is "Prelude.List" leads to
-- current namespace of "Prelude.List.Data"
-- Inner namespaces go first, for ease of name lookup
export
extendNS : {auto c : Ref Ctxt Defs} ->
           List String -> Core annot ()
extendNS ns
    = do defs <- get Ctxt
         put Ctxt (record { currentNS $= ((reverse ns) ++) } defs)

-- Get the name as it would be defined in the current namespace
-- i.e. if it doesn't have an explicit namespace already, add it,
-- otherwise leave it alone
export
inCurrentNS : {auto c : Ref Ctxt Defs} ->
              Name -> Core annot Name
inCurrentNS (UN n)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) (UN n))
inCurrentNS n@(MN _ _)
    = do defs <- get Ctxt
         pure (NS (currentNS defs) n)
inCurrentNS n = pure n

-- Note that the name should be saved when writing out a .ttc
export
addToSave : {auto c : Ref Ctxt Defs} ->
            Name -> Core annot ()
addToSave n
    = do defs <- get Ctxt
         put Ctxt (record { toSave $= insert n } defs)

-- Clear the names to save when writing out a .tti
export
clearToSave : {auto c : Ref Ctxt Defs} ->
              Core annot ()
clearToSave
    = do defs <- get Ctxt
         put Ctxt (record { toSave = empty } defs)

export
getNextTypeTag : {auto x : Ref Ctxt Defs} ->
								 Core annot Int
getNextTypeTag
    = do defs <- get Ctxt
         let t = nextTag defs
         put Ctxt (record { nextTag = t + 1 } defs)
         pure t

export
getNextHole : {auto x : Ref Ctxt Defs} -> Core annot Int
getNextHole
    = do defs <- get Ctxt
         let t = nextHole defs
         put Ctxt (record { nextHole = t + 1 } defs)
         pure t

export
genName : {auto x : Ref Ctxt Defs} ->
					String -> Core annot Name
genName root
    = do ust <- get Ctxt
         put Ctxt (record { nextVar $= (+1) } ust)
         inCurrentNS (MN root (nextVar ust))

export
genVarName : {auto x : Ref Ctxt Defs} ->
					String -> Core annot Name
genVarName root
    = do ust <- get Ctxt
         put Ctxt (record { nextVar $= (+1) } ust)
         pure (MN root (nextVar ust))

export
genCaseName : {auto x : Ref Ctxt Defs} ->
			     		Name -> Core annot Name
genCaseName root
    = do ust <- get Ctxt
         put Ctxt (record { nextVar $= (+1) } ust)
         pure (GN (CaseBlock root (nextVar ust)))

export
genWithName : {auto x : Ref Ctxt Defs} ->
			     		Name -> Core annot Name
genWithName root
    = do ust <- get Ctxt
         put Ctxt (record { nextVar $= (+1) } ust)
         pure (GN (WithBlock root (nextVar ust)))

export
getNextVar : {auto x : Ref Ctxt Defs} ->
			     	 Core annot Int
getNextVar
    = do ust <- get Ctxt
         put Ctxt (record { nextVar $= (+1) } ust)
         pure (nextVar ust)

export
setCtxt : {auto x : Ref Ctxt Defs} -> Gamma -> Core annot ()
setCtxt gam
    = do st <- get Ctxt
         put Ctxt (record { gamma = gam } st)

export
getDescendents : Name -> Gamma -> List Name
getDescendents n g
    = CSet.toList $ getAllDesc [n] empty g
  where
    getAllDesc : List Name -> SortedSet -> Gamma -> SortedSet
    getAllDesc [] ns g = ns
    getAllDesc (n :: rest) ns g
      = if contains n ns
           then getAllDesc rest ns g
           else case lookupGlobalExact n g of
                     Nothing => getAllDesc rest ns g
                     Just def => assert_total $
											 let refs = refersTo def in
												 getAllDesc (rest ++ refs)
						                        (union ns (fromList refs)) g

export
addDef : {auto x : Ref Ctxt Defs} -> Name -> GlobalDef -> Core annot ()
addDef n def
    = do g <- getCtxt 
         setCtxt (addCtxt n def g)

export
addBuiltin : {auto x : Ref Ctxt Defs} -> 
             Name -> ClosedTerm -> Totality ->
             PrimFn arity -> Core annot ()
addBuiltin n ty tot op 
    = addDef n (MkGlobalDef ty RigW [] Public tot [Inline] (Builtin op) Nothing [])

export
updateDef : {auto x : Ref Ctxt Defs} ->
						Name -> (Def -> Maybe Def) -> Core annot ()
updateDef n fdef 
    = do g <- getCtxt
         case lookupCtxtExact n g of
              Nothing => pure ()
              Just odef => 
                   case fdef (definition odef) of
                        Nothing => pure ()
                        Just newdef =>
                            let gdef = record { definition = newdef,
                                                refersTo = getRefs newdef } odef in
                                setCtxt (addCtxt n gdef g)
 
export
updateTy : {auto x : Ref Ctxt Defs} ->
					Name -> ClosedTerm -> Core annot ()
updateTy n ty
    = do g <- getCtxt
         case lookupCtxtExact n g of
              Nothing => throw (InternalError ("No such name to update " ++ show n))
              Just odef => 
                   let gdef = record { type = ty } odef in
                       setCtxt (addCtxt n gdef g)

export
setCompiled : {auto x : Ref Ctxt Defs} ->
              Name -> CDef -> Core annot ()
setCompiled n cexp
    = do g <- getCtxt
         case lookupCtxtExact n g of
              Nothing => throw (InternalError ("No such name to compile " ++ show n))
              Just odef =>
                   let gdef = record { compexpr = Just cexp } odef in
                       setCtxt (addCtxt n gdef g)

-- Check that the names used in the term don't conflict with the visibility
-- of the name. No name in the term, defined in the same namespace,
-- can have lower visibility than the given name and visibility.
export
checkNameVisibility : {auto x : Ref Ctxt Defs} ->
                      annot -> 
                      Name -> Visibility -> Term vars -> Core annot ()
checkNameVisibility loc n vis tm
    = do traverse visible (toList (getRefs tm))
         pure ()
  where
    eqNS : Name -> Name -> Bool
    eqNS (NS xs _) (NS ys _) = xs == ys
    eqNS _ _ = False

    visible : Name -> Core annot ()
    visible ref
        = do defs <- get Ctxt
             case lookupGlobalExact ref (gamma defs) of
                  Just def =>
                       if visibility def < vis && eqNS n ref
                          then throw (VisibilityError loc vis n 
                                            (visibility def) ref)
                          else pure ()
                  Nothing => pure ()

-- Add a function definition, as long as the type exists already
export
addFnDef : {auto x : Ref Ctxt Defs} ->
					 annot -> Name -> CaseTree args -> CaseTree args -> 
           List (List Name, ClosedTerm, ClosedTerm) -> Core annot ()
addFnDef loc n treeCT treeRT pats
    = do ctxt <- get Ctxt
         case lookupGlobalExact n (gamma ctxt) of
              Just def => 
                 let def' = record { definition = PMDef False _ treeCT treeRT pats,
                                     refersTo = getRefs treeCT } def in
                     addDef n def'
              Nothing => throw (NoDeclaration loc n)
  where
    close : Int -> (plets : Bool) -> Env Term vars -> Term vars -> ClosedTerm
    close i plets [] tm = tm
    close i True (PLet c val ty :: bs) tm 
		    = close (i + 1) True bs (Bind (MN "pat" i) (Let c val ty) (renameTop _ tm))
    close i plets (b :: bs) tm 
        = close (i + 1) plets bs (subst (Ref Bound (MN "pat" i)) tm)

    toClosed : Clause -> (ClosedTerm, ClosedTerm)
    toClosed (MkClause env lhs rhs) 
          = (close 0 False env lhs, close 0 True env rhs)

-- If a name appears more than once in an argument list, only the first is
-- considered a parameter
dropReps : List (Maybe (Term vars)) -> List (Maybe (Term vars))
dropReps [] = []
dropReps {vars} (Just (Local r x) :: xs)
    = Just (Local r x) :: assert_total (dropReps (map toNothing xs))
  where
    toNothing : Maybe (Term vars) -> Maybe (Term vars)
    toNothing tm@(Just (Local r v'))
        = if sameVar x v' then Nothing else tm
    toNothing tm = tm
dropReps (x :: xs) = x :: dropReps xs

updateParams : Maybe (List (Maybe (Term vars))) -> 
                  -- arguments to the type constructor which could be
                  -- parameters
                  -- Nothing, as an argument, means this argument can't
                  -- be a parameter position
               List (Term vars) ->
                  -- arguments to an application 
               List (Maybe (Term vars))
updateParams Nothing args = dropReps $ map couldBeParam args
  where
    couldBeParam : Term vars -> Maybe (Term vars)
    couldBeParam (Local r v) = Just (Local r v)
    couldBeParam _ = Nothing
updateParams (Just args) args' = dropReps $ zipWith mergeArg args args'
  where
    mergeArg : Maybe (Term vars) -> Term vars -> Maybe (Term vars)
    mergeArg (Just (Local r x)) (Local r' y)
        = if sameVar x y then Just (Local r x) else Nothing
    mergeArg _ _ = Nothing

getPs : Maybe (List (Maybe (Term vars))) -> Name -> Term vars ->
           Maybe (List (Maybe (Term vars)))
getPs acc tyn (Bind x (Pi _ _ ty) sc)
      = let scPs = getPs (map (map (map weaken)) acc) tyn sc in
            map (map shrink) scPs
  where
    shrink : Maybe (Term (x :: vars)) -> Maybe (Term vars)
    shrink Nothing = Nothing
    shrink (Just tm) = shrinkTerm tm (DropCons SubRefl)
getPs acc tyn tm with (unapply tm)
  getPs acc tyn (apply (Ref _ n) args) | ArgsList 
      = if n == tyn 
           then Just (updateParams acc args)
           else acc
  getPs acc tyn (apply f args) | ArgsList = acc

toPos : Maybe (List (Maybe a)) -> List Nat
toPos Nothing = []
toPos (Just ns) = justPos 0 ns
  where
    justPos : Nat -> List (Maybe a) -> List Nat
    justPos i [] = []
    justPos i (Just x :: xs) = i :: justPos (1 + i) xs
    justPos i (Nothing :: xs) = justPos (1 + i) xs

getConPs : Maybe (List (Maybe (Term vars))) -> Name -> Term vars -> List Nat
getConPs acc tyn (Bind x (Pi _ _ ty) sc) 
    = let bacc = getPs acc tyn ty in
          getConPs (map (map (map weaken)) bacc) tyn sc
getConPs acc tyn tm = toPos (getPs acc tyn tm)
    
combinePos : Eq a => List (List a) -> List a
combinePos [] = []
combinePos (xs :: xss) = filter (\x => all (elem x) xss) xs

paramPos : Name -> (dcons : List ClosedTerm) ->
           List Nat
paramPos tyn dcons = combinePos (map (getConPs Nothing tyn) dcons)

export
addData : {auto x : Ref Ctxt Defs} ->
					List Name -> Visibility -> DataDef -> Core annot ()
addData vs vis (MkData (MkCon tyn arity tycon) datacons)
    = do gam <- getCtxt 
         tag <- getNextTypeTag 
         let tydef = newDef vs tycon vis (TCon tag arity 
                                         (paramPos tyn (map type datacons))
                                         (allDet arity)
                                         (map name datacons))
         let gam' = addCtxt tyn tydef gam
         setCtxt (addDataConstructors 0 datacons gam')
  where
    allDet : Nat -> List Nat
    allDet Z = []
    allDet (S k) = [0..k]

    conVisibility : Visibility -> Visibility
    conVisibility Export = Private
    conVisibility x = x
    
    findGuarded : AList Nat vars -> Term vars -> List Nat
    findGuarded as tm with (unapply tm)
      findGuarded as (apply (Ref (DataCon _ _) _) args) | ArgsList 
			     = nub $ assert_total (concatMap (findGuarded as) args)
      findGuarded as (apply (Ref (TyCon _ _) _) args) | ArgsList 
			     = nub $ assert_total (concatMap (findGuarded as) args)
      findGuarded as (apply (Local {x} r var) []) | ArgsList
	         = [getCorresponding as var]
      findGuarded as (apply f args) | ArgsList 
			     = []

		-- Calculate which argument positions in the type are 'forced'.
		-- An argument is forced if it appears guarded by constructors in one
		-- of the parameters or indices of the constructor's return type
    forcedPos : (pos : Nat) -> AList Nat vars -> Term vars -> List Nat
    forcedPos p as (Bind x (Pi _ _ ty) sc)
        = forcedPos (p + 1) (p :: as) sc
    forcedPos p as tm = findGuarded as tm

    addDataConstructors : (tag : Int) -> 
                          List Constructor -> Gamma -> Gamma
    addDataConstructors tag [] gam = gam
    addDataConstructors tag (MkCon n a ty :: cs) gam
        = do let condef = newDef vs ty (conVisibility vis) 
						                     (DCon tag a (forcedPos 0 [] ty))
             let gam' = addCtxt n condef gam
             addDataConstructors (tag + 1) cs gam'

public export
record SearchData where
  constructor MkSearchData
  detArgs : List Nat -- determining argument positions
  globalHints : List Name -- global (non type specific) hints
  directHints : List Name -- type name hints
  indirectHints : List Name -- hints for a type 'b', with a type of the form 'a -> b'

-- Get the auto search data for a name. That's: determining arguments
-- (the first element), the open hints (the second element) 
-- and all the other names that might solve a goal
-- of the given type (constructors, local hints, global hints, in that order)
export
getSearchData : {auto x : Ref Ctxt Defs} ->
                annot -> Bool -> Name -> 
                Core annot SearchData
getSearchData loc a target
    = do defs <- get Ctxt
         case lookupDefExact target (gamma defs) of
              Just (TCon _ _ _ dets cons) => 
                   do let hs = case lookupCtxtExact target (typeHints defs) of
                                    Nothing => []
                                    Just ns => ns
                      pure (if a then MkSearchData dets (openHints defs) 
                                      (map fst (filter direct hs))
                                      (map fst (filter (not . direct) hs))
                                 -- no determining args for defaults
                                 else MkSearchData [] [] (openAutoHints defs) [])
              _ => throw (UndefinedName loc target)
  where
    direct : (Name, Bool) -> Bool
    direct = snd

    openAutoHints : Defs -> List Name
    openAutoHints defs
        = let hs = autoHints defs in
              map snd (filter (\t => fst t == a) hs)

export
setDetermining : {auto x : Ref Ctxt Defs} ->
                 annot -> Name -> List Name -> Core annot ()
setDetermining loc tn args
    = do defs <- get Ctxt
         case lookupGlobalExact tn (gamma defs) of
              Just g =>
                   case definition g of
                        TCon t a ps _ cons =>
                          do apos <- getPos 0 args (type g)
                             let g' = record { definition = 
                                                TCon t a ps apos cons } g
                             put Ctxt (record { gamma $= addCtxt tn g' } defs)
                        _ => throw (UndefinedName loc tn)
              _ => throw (UndefinedName loc tn)
  where
    -- Type isn't normalised, but the argument names refer to those given 
    -- explicitly in the type, so there's no need.
    getPos : Nat -> List Name -> Term vs -> Core annot (List Nat)
    getPos i ns (Bind x (Pi _ _ _) sc)
        = if x `elem` ns 
             then do rest <- getPos (1 + i) (filter (/=x) ns) sc
                     pure $ i :: rest
             else getPos (1 + i) ns sc

    getPos _ [] _ = pure []
    getPos _ ns ty = throw (GenericMsg loc ("Unknown determining arguments: "
                           ++ showSep ", " (map show ns)))

export
runWithCtxt : Show annot => Core annot () -> IO ()
runWithCtxt prog = coreRun prog 
                           (\err => printLn err)
                           (\ok => pure ())

-- Return whether an argument to the given term would be a forced argument
export
isForcedArg : Gamma -> Term vars -> Bool
isForcedArg gam tm with (unapply tm)
  isForcedArg gam (apply (Ref (DataCon _ _) n) args) | ArgsList 
      = case lookupDefExact n gam of
             Just (DCon _ _ forcedpos)
						    -- if the number of args so far is in forcedpos, then
								-- the next argument position is indeed forced
                   => length args `elem` forcedpos
             _ => False
  isForcedArg gam (apply f args) | ArgsList = False

export
setFlag : {auto x : Ref Ctxt Defs} ->
					annot -> Name -> DefFlag -> Core annot ()
setFlag loc n fl
    = do ctxt <- getCtxt
         case lookupGlobalExact n ctxt of
              Nothing => throw (UndefinedName loc n)
              Just def =>
                   do let flags' = fl :: filter (/= fl) (flags def)
                      addDef n (record { flags = flags' } def)

export
setNameFlag : {auto x : Ref Ctxt Defs} ->
			    		annot -> Name -> DefFlag -> Core annot ()
setNameFlag loc n fl
    = do ctxt <- getCtxt
         case lookupGlobalName n ctxt of
              [] => throw (UndefinedName loc n)
              [(n', def)] =>
                   do let flags' = fl :: filter (/= fl) (flags def)
                      addDef n' (record { flags = flags' } def)
              res => throw (AmbiguousName loc (map fst res))


export
unsetFlag : {auto x : Ref Ctxt Defs} ->
            annot -> Name -> DefFlag -> Core annot ()
unsetFlag loc n fl
    = do ctxt <- getCtxt
         case lookupGlobalExact n ctxt of
              Nothing => throw (UndefinedName loc n)
              Just def =>
                   do let flags' = filter (/= fl) (flags def)
                      addDef n (record { flags = flags' } def)

export
hasFlag : {auto x : Ref Ctxt Defs} ->
          annot -> Name -> DefFlag -> Core annot Bool
hasFlag loc n fl
    = do ctxt <- getCtxt
         case lookupGlobalExact n ctxt of
              Nothing => throw (UndefinedName loc n)
              Just def => pure (fl `elem` flags def)

export
setTotality : {auto x : Ref Ctxt Defs} ->
              annot -> Name -> Totality -> Core annot ()
setTotality loc n tot
    = do ctxt <- getCtxt
         case lookupGlobalExact n ctxt of
              Nothing => throw (UndefinedName loc n)
              Just def => 
                   addDef n (record { totality = tot } def)

export
getTotality : {auto x : Ref Ctxt Defs} ->
              annot -> Name -> Core annot Totality
getTotality loc n
    = do ctxt <- getCtxt
         case lookupGlobalExact n ctxt of
              Nothing => throw (UndefinedName loc n)
              Just def => pure $ totality def

export
setVisibility : {auto x : Ref Ctxt Defs} ->
                annot -> Name -> Visibility -> Core annot ()
setVisibility loc n vis
    = do ctxt <- getCtxt
         case lookupGlobalExact n ctxt of
              Nothing => throw (UndefinedName loc n)
              Just def => 
                   addDef n (record { visibility = vis } def)

-- Set a name as Private that was previously visible (and, if 'everywhere' is
-- set, hide in any modules imported by this one)
export
hide : {auto x : Ref Ctxt Defs} ->
       annot -> (everywhere : Bool) -> Name -> Core annot ()
hide loc everywhere n
    = do ctxt <- getCtxt
         case lookupGlobalName n ctxt of
              [] => throw (UndefinedName loc n)
              [(nsn, _)] => do setVisibility loc nsn Private
                               defs <- get Ctxt
                               when everywhere $
                                  put Ctxt (record { hiddenNames $= (nsn ::) } defs)
              res => throw (AmbiguousName loc (map fst res))

export
getVisibility : {auto x : Ref Ctxt Defs} ->
                annot -> Name -> Core annot Visibility
getVisibility loc n
    = do ctxt <- getCtxt
         case lookupGlobalExact n ctxt of
              Nothing => throw (UndefinedName loc n)
              Just def => pure $ visibility def

export
isTotal : {auto x : Ref Ctxt Defs} ->
          annot -> Name -> Core annot Bool
isTotal loc n
    = do t <- getTotality loc n
         case t of
              Total => pure True
              _ => pure False


export
addToTypeHints : Name -> Name -> Bool -> Defs -> Defs
addToTypeHints ty hint direct defs
    = let hs : List (Name, Bool)
             = case lookupCtxtExact ty (typeHints defs) of
                    Nothing => []
                    Just ns => ns in
          record { typeHints $= addCtxt ty ((hint, direct) :: hs) } defs

export
addHintFor : {auto x : Ref Ctxt Defs} ->
					   annot -> Name -> Name -> Bool -> Core annot ()
addHintFor loc ty hint direct
    = do defs <- get Ctxt
         put Ctxt (addToTypeHints ty hint direct defs)
         setFlag loc hint (TypeHint ty direct)

export
addGlobalHint : {auto x : Ref Ctxt Defs} ->
					      annot -> Bool -> Name -> Core annot ()
addGlobalHint loc a hint
    = do d <- get Ctxt
         put Ctxt (record { autoHints $= ((a, hint) ::) } d)
         setFlag loc hint (GlobalHint a)

export
addOpenHint : {auto x : Ref Ctxt Defs} -> Name -> Core annot ()
addOpenHint hint
    = do d <- get Ctxt
         put Ctxt (record { openHints $= (hint ::) } d)

export
setOpenHints : {auto x : Ref Ctxt Defs} -> List Name -> Core annot ()
setOpenHints hs
    = do d <- get Ctxt
         put Ctxt (record { openHints = hs } d)

processFlags : {auto c : Ref Ctxt Defs} ->
               annot -> (Name, GlobalDef) -> Core annot ()
processFlags loc (n, def)
    = do traverse processFlag (flags def)
         pure ()
  where
    processFlag : DefFlag -> Core annot ()
    processFlag (TypeHint ty d)
        = addHintFor loc ty n d
    processFlag (GlobalHint t)
        = addGlobalHint loc t n
    processFlag _ = pure () 

-- Extend the context with the definitions/options given in the second
-- New options override current ones
export
extend : {auto c : Ref Ctxt Defs} ->
         annot -> Bool -> Defs -> Core annot ()
extend loc reexp new
    = do ctxt <- get Ctxt
         -- Only pass on the hidden names if imported directly
         let hidden = if reexp then nub (hiddenNames ctxt ++ hiddenNames new)
                               else hiddenNames ctxt
         put Ctxt (record { gamma $= mergeContext (gamma new),
                            options $= mergeOptions (options new),
                            hiddenNames = hidden,
                            cgdirectives $= (++ cgdirectives new)
                          } ctxt)
         -- Process any flags that need processing in the newly added
         -- thing (e.g. whether they are search hints)
         traverse (processFlags loc) (toList (gamma new))
         pure ()

-- TODO: Need to do the actual renaming in mergeContextAs and before processFlags!
export
extendAs : {auto c : Ref Ctxt Defs} ->
           annot -> Bool -> List String -> List String -> 
           Defs -> Core annot ()
extendAs loc reexp modNS importAs new
    = if modNS == importAs 
         then extend loc reexp new
         else do ctxt <- get Ctxt
                 -- Only pass on the hidden names if imported directly
                 let hidden = if reexp then nub (hiddenNames ctxt ++ hiddenNames new)
                                       else hiddenNames ctxt
                 put Ctxt (record { gamma $= mergeContextAs modNS importAs (gamma new),
                                    options $= mergeOptions (options new),
                                    hiddenNames = hidden,
                                    cgdirectives $= (++ cgdirectives new)
                                  } ctxt)
                 -- Process any flags that need processing in the newly added
                 -- thing (e.g. whether they are search hints)
                 traverse (processFlags loc) (toList (gamma new))
                 pure ()

