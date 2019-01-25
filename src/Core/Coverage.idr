module Core.Coverage

import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT

import Control.Monad.State
import Data.List

%default covering

-- Return whether any part of the type conflicts in such a way that they
-- can't possibly be equal (i.e. mismatched constructor)
conflict : Defs -> NF vars -> Name -> Bool
conflict defs nfty n
    = case lookupDefTyExact n (gamma defs) of
           Just (DCon t arity _, dty)
                => conflictNF nfty (nf defs [] dty)
           _ => False
  where
    mutual
      conflictArgs : List (Closure vars) -> List (Closure []) -> Bool
      conflictArgs [] [] = False
      conflictArgs (c :: cs) (c' :: cs')
          = let cnf = evalClosure defs c
                cnf' = evalClosure defs c' in
                conflictNF cnf cnf' || conflictArgs cs cs'
      conflictArgs _ _ = False

      conflictNF : NF vars -> NF [] -> Bool
      conflictNF t (NBind x b sc)
          = conflictNF t (sc (toClosure defaultOpts [] Erased))
      conflictNF (NDCon n t a args) (NDCon n' t' a' args')
          = if t == t'
               then conflictArgs args args'
               else True
      conflictNF (NTCon n t a args) (NTCon n' t' a' args')
          = if n == n'
               then conflictArgs args args'
               else True
      conflictNF (NPrimVal c) (NPrimVal c') = c /= c'
      conflictNF _ _ = False

-- Return whether the given type is definitely empty (due to there being
-- no constructors which can possibly match it.)
export
isEmpty : Defs -> NF vars -> Bool
isEmpty defs (NTCon n t a args)
     = case lookupDefExact n (gamma defs) of
            Just (TCon _ _ _ _ _ cons)
                 => all (conflict defs (NTCon n t a args)) cons
            _ => False
isEmpty defs _ = False

-- Need this to get a NF from a Term; the names are free in any case
freeEnv : (vs : List Name) -> Env Term vs
freeEnv [] = []
freeEnv (n :: ns) = PVar RigW Erased :: freeEnv ns

-- Given a normalised type, get all the possible constructors for that
-- type family, with their type, name, tag, and arity
getCons : Defs -> NF vars -> List (NF [], Name, Int, Nat)
getCons defs (NTCon tn _ _ _)
    = case lookupDefExact tn (gamma defs) of
           Just (TCon _ _ _ _ _ cons) => mapMaybe addTy cons
           _ => []
  where
    addTy : Name -> Maybe (NF [], Name, Int, Nat)
    addTy cn
        = case lookupDefTyExact cn (gamma defs) of
               Just (DCon t arity _, ty) => Just (nf defs [] ty, cn, t, arity)
               _ => Nothing
getCons defs _ = []

mutual
  matchArgs : Defs -> List (Closure vars) -> List (Closure []) -> Bool
  matchArgs defs [] [] = True
  matchArgs defs (c :: cs) (c' :: cs') 
      = let cnf = evalClosure defs c 
            cnf' = evalClosure defs c' in
            matchNF defs cnf cnf' && matchArgs defs cs cs'
  matchArgs defs _ _ = False

  -- Is the first type a possible match for a constructor of the second type?
  matchNF : Defs -> NF vars -> NF [] -> Bool
  matchNF defs t (NBind x b sc)
     = matchNF defs t (sc (toClosure defaultOpts [] Erased))
  matchNF defs (NDCon n t a args) (NDCon n' t' a' args')
     = if t == t'
          then matchArgs defs args args'
          else False
  matchNF defs (NTCon n t a args) (NTCon n' t' a' args')
     = if n == n'
          then matchArgs defs args args'
          else False
  matchNF defs (NPrimVal c) (NPrimVal c') = c == c'
  matchNF _ _ _ = True

emptyRHS : CaseTree vars -> CaseTree vars
emptyRHS (Case el sc alts) = Case el sc (map emptyRHSalt alts)
  where
    emptyRHSalt : CaseAlt vars -> CaseAlt vars
    emptyRHSalt (ConCase n t args sc) = ConCase n t args (emptyRHS sc)
    emptyRHSalt (ConstCase c sc) = ConstCase c (emptyRHS sc)
    emptyRHSalt (DefaultCase sc) = DefaultCase (emptyRHS sc)
emptyRHS (STerm s) = STerm Erased
emptyRHS sc = sc

mkAlt : CaseTree vars -> (Name, Int, Nat) -> CaseAlt vars
mkAlt sc (cn, t, ar)
    = ConCase cn t (map (MN "m") (take ar [0..])) (weakenNs _ (emptyRHS sc))

altMatch : CaseAlt vars -> CaseAlt vars -> Bool
altMatch _ (DefaultCase _) = True
altMatch (ConCase _ t _ _) (ConCase _ t' _ _) = t == t'
altMatch (ConstCase c _) (ConstCase c' _) = c == c'
altMatch _ _ = False

-- Given a type and a list of case alternatives, return the
-- well-typed alternatives which were *not* in the list
getMissingAlts : Defs -> NF vars -> List (CaseAlt vars) -> List (CaseAlt vars)
-- If it's a primitive, there's too many to reasonably check, so require a 
-- catch all
getMissingAlts defs (NPrimVal c) alts
    = if any isDefault alts
         then []
         else [DefaultCase (Unmatched "Coverage check")]
  where
    isDefault : CaseAlt vars -> Bool
    isDefault (DefaultCase _) = True
    isDefault _ = False
-- Similarly for types
getMissingAlts defs NType alts
    = if any isDefault alts
         then []
         else [DefaultCase (Unmatched "Coverage check")]
  where
    isDefault : CaseAlt vars -> Bool
    isDefault (DefaultCase _) = True
    isDefault _ = False
getMissingAlts defs nfty alts  
    = let allCons = getCons defs nfty 
          validCons = filter (\x => matchNF defs nfty (fst x)) allCons in
          filter (noneOf alts) (map (mkAlt (Unmatched "Coverage check") . snd) validCons)
  where
    -- Return whether the alternative c matches none of the given cases in alts
    noneOf : List (CaseAlt vars) -> CaseAlt vars -> Bool
    noneOf alts c = not $ any (altMatch c) alts 

-- Mapping of variable to constructor tag already matched for it
KnownVars : List Name -> Type -> Type
KnownVars vars a = List (var ** (Elem var vars, a))

showK : Show a => KnownVars ns a -> String
showK {a} xs = show (map aString xs)
  where
    aString : (var : Name ** (Elem var vars, a)) -> (Name, a)
    aString (v ** (_, t)) = (v, t)

weakenNs : (args : List Name) -> KnownVars vars a -> KnownVars (args ++ vars) a
weakenNs args [] = []
weakenNs args ((var ** (el, t)) :: xs) 
    = (var ** (insertElemNames {outer = []} args el, t)) :: weakenNs args xs

findTag : Elem var vars -> KnownVars vars a -> Maybe a
findTag el [] = Nothing
findTag el ((_ ** (el', t)) :: xs)
    = if sameVar el el'
         then Just t
         else findTag el xs

addNot : Elem var vars -> Int -> KnownVars vars (List Int) ->
         KnownVars vars (List Int)
addNot el t [] = [(_ ** (el, [t]))]
addNot el t ((_ ** (el', ts)) :: xs)
    = if sameVar el el'
         then ((_ ** (el', t :: ts)) :: xs)
         else ((_ ** (el', ts)) :: addNot el t xs)

tagIs : Int -> CaseAlt vars -> Bool
tagIs t (ConCase _ t' _ _) = t == t'
tagIs t (ConstCase _ _) = False
tagIs t (DefaultCase _) = True

tagIsNot : List Int -> CaseAlt vars -> Bool
tagIsNot ts (ConCase _ t' _ _) = not (t' `elem` ts)
tagIsNot ts (ConstCase _ _) = True
tagIsNot ts (DefaultCase _) = False

-- Replace a default case with explicit branches for the constructors.
-- This is easier than checking whether a default is needed when traversing
-- the tree (just one constructor lookup up front).
replaceDefaults : Defs -> NF vars -> List (CaseAlt vars) -> List (CaseAlt vars)
-- Leave it alone if it's a primitive type though, since we need the catch
-- all case there
replaceDefaults defs (NPrimVal _) cs = cs
replaceDefaults defs nfty cs = dropRep (concatMap rep cs)
  where
    rep : CaseAlt vars -> List (CaseAlt vars)
    rep (DefaultCase sc)
        = let allCons = getCons defs nfty in
              map (mkAlt sc . snd) allCons
    rep c = [c]

    dropRep : List (CaseAlt vars) -> List (CaseAlt vars)
    dropRep [] = []
    dropRep (c@(ConCase n t args sc) :: rest)
          -- assumption is that there's no defaultcase in 'rest' because
          -- we've just removed it
        = c :: dropRep (filter (not . tagIs t) rest)
    dropRep (c :: rest) = c :: dropRep rest


-- Traverse a case tree and refine the arguments while matching, so that
-- when we reach a leaf we know what patterns were used to get there,
-- and return those patterns.
-- The returned patterns are those arising from the *missing* cases
buildArgs : Defs ->
            KnownVars vars Int -> -- Things which have definitely match
            KnownVars vars (List Int) -> -- Things an argument *can't* be
                                    -- (because a previous case matches)
            List ClosedTerm -> -- ^ arguments, with explicit names
            CaseTree vars -> List (List ClosedTerm)
buildArgs defs known not ps cs@(Case {var} el ty altsIn)
  -- If we've already matched on 'el' in this branch, restrict the alternatives
  -- to the tag we already know. Otherwise, add missing cases and filter out
  -- the ones it can't possibly be (the 'not') because a previous case
  -- has matched.
    = let fenv = freeEnv _
          nfty = nf defs fenv ty 
          alts = replaceDefaults defs nfty altsIn
          alts' = alts ++ getMissingAlts defs nfty alts
          altsK = maybe alts' (\t => filter (tagIs t) alts')
                              (findTag el known) 
          altsN = maybe altsK (\ts => filter (tagIsNot ts) altsK)
                              (findTag el not) in
          buildArgsAlt not altsN
  where
    buildArgAlt : KnownVars vars (List Int) ->
                  CaseAlt vars -> List (List ClosedTerm)
    buildArgAlt not' (ConCase n t args sc) 
        = let con = Ref (DataCon t (length args)) n
              ps' = map (substName var (apply con (map (Ref Bound) args))) ps in
              buildArgs defs (weakenNs args ((_ ** (el, t)) :: known)) 
                             (weakenNs args not') ps' sc
    buildArgAlt not' (ConstCase c sc) 
        = let ps' = map (substName var (PrimVal c)) ps in
              buildArgs defs known not' ps' sc
    buildArgAlt not' (DefaultCase sc) = buildArgs defs known not' ps sc

    buildArgsAlt : KnownVars vars (List Int) -> List (CaseAlt vars) ->
                   List (List ClosedTerm)
    buildArgsAlt not' [] = []
    buildArgsAlt not' (c@(ConCase _ t _ _) :: cs)
        = buildArgAlt not' c ++ buildArgsAlt (addNot el t not') cs
    buildArgsAlt not' (c :: cs)
        = buildArgAlt not' c ++ buildArgsAlt not' cs

buildArgs defs known not ps (STerm vs) 
    = [] -- matched, so return nothing
buildArgs defs known not ps (Unmatched msg) 
    = [ps] -- unmatched, so return it
buildArgs defs known not ps Impossible 
    = [] -- not a possible match, so return nothing

-- Traverse a case tree and return pattern clauses which are not
-- matched. These might still be invalid patterns, or patterns which are covered
-- elsewhere (turning up due to overlapping clauses) so the results should be
-- checked
export
getMissing : {auto c : Ref Ctxt Defs} ->
             Name -> CaseTree vars -> Core annot (List ClosedTerm)
getMissing n ctree
   = do defs <- get Ctxt
        let psIn = map (Ref Bound) vars
        let pats = buildArgs defs [] [] psIn ctree
        pure (map (apply (Ref Func n)) pats)

-- For the given name, get the names it refers to which are not themselves
-- covering
export
getNonCoveringRefs : {auto c : Ref Ctxt Defs} ->
                     annot -> Name -> Core annot (List Name)
getNonCoveringRefs loc n
   = do defs <- get Ctxt
        let Just d = lookupGlobalExact n (gamma defs)
           | Nothing => throw (UndefinedName loc n)
        pure $ filter (notCovering defs) (refersTo d)
  where
    notCovering : Defs -> Name -> Bool
    notCovering defs n
        = case lookupGlobalExact n (gamma defs) of
               Just def => case isCovering (totality def) of
                                IsCovering => False
                                _ => True
               _ => False
