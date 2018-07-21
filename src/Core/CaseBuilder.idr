module Core.CaseBuilder

import public Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT

import Control.Monad.State
import Data.List

%default covering

data ArgType : List Name -> Type where
     Known : RigCount -> (ty : Term vars) -> ArgType vars -- arg has type 'ty'
     Stuck : (fty : Term vars) -> ArgType vars 
         -- ^ arg will have argument type of 'fty' when we know enough to
         -- calculate it
     Unknown : ArgType vars
         -- arg's type is not yet known due to a previously stuck argument

Show (ArgType ns) where
  show (Known c t) = "Known " ++ show c ++ " " ++ show t
  show (Stuck t) = "Stuck " ++ show t
  show Unknown = "Unknown"

record PatInfo (pvar : Name) (vars : List Name) where
  constructor MkInfo
  pat : Pat
  loc : Elem pvar vars
  argType : ArgType vars -- Type of the argument being inspected (i.e. 
                         -- *not* refined by this particular pattern)

{-
NamedPats is a list of patterns on the LHS of a clause. Each entry in
the list gives a pattern, and a proof that there is a variable we can
inspect to see if it matches the pattern.

A definition consists of a list of clauses, which are a 'NamedPats' and
a term on the RHS. There is an assumption that corresponding positions in
NamedPats always have the same 'Elem' proof, though this isn't expressed in
a type anywhere.
-}

data NamedPats : List Name -> -- pattern variables still to process
                 List Name -> -- the pattern variables still to process,
                              -- in order
                 Type where
     Nil : NamedPats vars []
     (::) : PatInfo pvar vars -> 
            -- ^ a pattern, where its variable appears in the vars list,
            -- and its type. The type has no variable names; any names it
            -- refers to are explicit
            NamedPats vars ns -> NamedPats vars (pvar :: ns)

updatePats : Env Term vars -> 
             NF vars -> NamedPats vars todo -> NamedPats vars todo
updatePats env nf [] = []
updatePats {todo = pvar :: ns} env (NBind _ (Pi c _ farg) fsc) (p :: ps)
  = case argType p of
         Unknown =>
            record { argType = Known c (quote initCtxt env farg) } p
              :: updatePats env (fsc (toClosure False env (Ref Bound pvar))) ps
         _ => p :: ps
updatePats env nf (p :: ps)
  = case argType p of
         Unknown => record { argType = Stuck (quote initCtxt env nf) } p :: ps
         _ => p :: ps

mkEnv : (vs : List Name) -> Env Term vs
mkEnv [] = []
mkEnv (n :: ns) = PVar RigW Erased :: mkEnv ns

substInPatInfo : Defs -> Name -> Term vars -> PatInfo pvar vars -> 
                 NamedPats vars todo -> (PatInfo pvar vars, NamedPats vars todo)
substInPatInfo {pvar} {vars} defs n tm p ps 
    = case argType p of
           Known c ty => (record { argType = Known c (substName n tm ty) } p, ps)
           Stuck fty => let env = mkEnv vars in
                          case nf defs env (substName n tm fty) of
                             NBind _ (Pi c _ farg) fsc =>
                               (record { argType = Known c (quote initCtxt env farg) } p,
                                   updatePats env 
                                      (fsc (toClosure False env
                                                (Ref Bound pvar))) ps)
           Unknown => (p, ps)

-- Substitute the name with a term in the pattern types, and reduce further
-- (this aims to resolve any 'Stuck' pattern types)
substInPats : Defs -> Name -> Term vars -> NamedPats vars todo -> NamedPats vars todo
substInPats defs n tm [] = []
substInPats defs n tm (p :: ps) 
    = let (p', ps') = substInPatInfo defs n tm p ps in
          p' :: substInPats defs n tm ps'

getPat : Elem x ps -> NamedPats ns ps -> PatInfo x ns
getPat Here (x :: xs) = x
getPat (There later) (x :: xs) = getPat later xs

dropPat : (el : Elem x ps) -> NamedPats ns ps -> NamedPats ns (dropElem ps el)
dropPat Here (x :: xs) = xs
dropPat (There later) (x :: xs) = x :: dropPat later xs

Show (NamedPats vars todo) where
  show xs = "[" ++ showAll xs ++ "]"
    where
      showAll : NamedPats vs ts -> String
      showAll [] = ""
      showAll {ts = t :: _ } [x]
          = show t ++ " " ++ show (pat x) ++ " [" ++ show (argType x) ++ "]" 
      showAll {ts = t :: _ } (x :: xs) 
          = show t ++ " " ++ show (pat x) ++ " [" ++ show (argType x) ++ "]"
                     ++ ", " ++ showAll xs

Weaken ArgType where
  weaken (Known c ty) = Known c (weaken ty)
  weaken (Stuck fty) = Stuck (weaken fty)
  weaken Unknown = Unknown

Weaken (PatInfo p) where
  weaken (MkInfo p el fty) = MkInfo p (There el) (weaken fty)

-- FIXME: oops, 'vars' should be second argument so we can use Weaken interface
weaken : NamedPats vars todo -> NamedPats (x :: vars) todo
weaken [] = []
weaken (p :: ps) = weaken p :: weaken ps

weakenNs : (ns : List Name) -> 
           NamedPats vars todo -> NamedPats (ns ++ vars) todo
weakenNs ns [] = []
weakenNs ns (p :: ps) 
    = weakenNs ns p :: weakenNs ns ps

(++) : NamedPats vars ms -> NamedPats vars ns -> NamedPats vars (ms ++ ns)
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

tail : NamedPats vars (p :: ps) -> NamedPats vars ps
tail (x :: xs) = xs

take : (as : List Name) -> NamedPats vars (as ++ bs) -> NamedPats vars as
take [] ps = []
take (x :: xs) (p :: ps) = p :: take xs ps

data PatClause : (vars : List Name) -> (todo : List Name) -> Type where
     MkPatClause : NamedPats vars todo -> 
                   (rhs : Term vars) -> PatClause vars todo

getNPs : PatClause vars todo -> NamedPats vars todo
getNPs (MkPatClause lhs rhs) = lhs

Show (PatClause vars todo) where
  show (MkPatClause ps rhs) 
     = show ps ++ " => " ++ show rhs

substInClause : Defs -> PatClause vars (a :: todo) -> PatClause vars (a :: todo)
substInClause {vars} {a} defs (MkPatClause (MkInfo pat pprf fty :: pats) rhs)
    = MkPatClause (MkInfo pat pprf fty :: 
                     substInPats defs a (mkTerm vars pat) pats) rhs

data LengthMatch : List a -> List b -> Type where
     NilMatch : LengthMatch [] []
     ConsMatch : LengthMatch xs ys -> LengthMatch (x :: xs) (y :: ys)

checkLengthMatch : (xs : List a) -> (ys : List b) -> Maybe (LengthMatch xs ys)
checkLengthMatch [] [] = Just NilMatch
checkLengthMatch [] (x :: xs) = Nothing
checkLengthMatch (x :: xs) [] = Nothing
checkLengthMatch (x :: xs) (y :: ys) 
    = Just (ConsMatch !(checkLengthMatch xs ys))

data Partitions : List (PatClause vars todo) -> Type where
     ConClauses : (cs : List (PatClause vars todo)) ->
                  Partitions ps -> Partitions (cs ++ ps)
     VarClauses : (vs : List (PatClause vars todo)) ->
                  Partitions ps -> Partitions (vs ++ ps)
     NoClauses : Partitions []

Show (Partitions ps) where
  show (ConClauses cs rest) = "CON " ++ show cs ++ ", " ++ show rest
  show (VarClauses vs rest) = "VAR " ++ show vs ++ ", " ++ show rest
  show NoClauses = "NONE"

data ClauseType = ConClause | VarClause

clauseType : PatClause vars (a :: as) -> ClauseType
-- If it's irrelevant, treat it as a variable
clauseType (MkPatClause (MkInfo _ _ (Known Rig0 t) :: _) rhs) = VarClause
clauseType (MkPatClause (MkInfo (PCon x y xs) _ _ :: _) rhs) = ConClause
clauseType (MkPatClause (MkInfo (PConst x) _ _ :: _) rhs) = ConClause
clauseType (MkPatClause (_ :: _) rhs) = VarClause

partition : (ps : List (PatClause vars (a :: as))) -> Partitions ps
partition [] = NoClauses
partition (x :: xs) with (partition xs)
  partition (x :: (cs ++ ps)) | (ConClauses cs rest) 
        = case clauseType x of
               ConClause => ConClauses (x :: cs) rest
               VarClause => VarClauses [x] (ConClauses cs rest)
  partition (x :: (vs ++ ps)) | (VarClauses vs rest) 
        = case clauseType x of
               ConClause => ConClauses [x] (VarClauses vs rest)
               VarClause => VarClauses (x :: vs) rest
  partition (x :: []) | NoClauses
        = case clauseType x of
               ConClause => ConClauses [x] NoClauses
               VarClause => VarClauses [x] NoClauses

data ConType : Type where
     CName : Name -> (tag : Int) -> ConType
     CConst : Constant -> ConType

conTypeEq : (x, y : ConType) -> Maybe (x = y)
conTypeEq (CName x tag) (CName x' tag') 
   = do Refl <- nameEq x x'
        case decEq tag tag' of
             Yes Refl => Just Refl
             No contra => Nothing
conTypeEq (CName x tag) (CConst y) = Nothing
conTypeEq (CConst x) (CName y tag) = Nothing
conTypeEq (CConst x) (CConst y) 
   = case constantEq x y of
          Nothing => Nothing
          Just Refl => Just Refl

data Group : List Name -> -- variables in scope
             List Name -> -- pattern variables still to process
             Type where
     ConGroup : Name -> (tag : Int) -> 
                List (PatClause (newargs ++ vars) (newargs ++ todo)) ->
                Group vars todo
     ConstGroup : Constant -> List (PatClause vars todo) ->
                  Group vars todo

Show (Group vars todo) where
  show (ConGroup c t cs) = "Con " ++ show c ++ ": " ++ show cs
  show (ConstGroup c cs) = "Const " ++ show c ++ ": " ++ show cs

data GroupMatch : ConType -> List Pat -> Group vars todo -> Type where
  ConMatch : LengthMatch ps newargs ->
             GroupMatch (CName n tag) ps 
               (ConGroup {newargs} n tag (MkPatClause pats rhs :: rest))
  ConstMatch : GroupMatch (CConst c) []
                  (ConstGroup c (MkPatClause pats rhs :: rest))
  NoMatch : GroupMatch ct ps g

checkGroupMatch : (c : ConType) -> (ps : List Pat) -> (g : Group vars todo) ->
                  GroupMatch c ps g
checkGroupMatch (CName x tag) ps (ConGroup {newargs} x' tag' (MkPatClause pats rhs :: rest)) 
    = case checkLengthMatch ps newargs of
           Nothing => NoMatch
           Just prf => case (nameEq x x', decEq tag tag') of
                            (Just Refl, Yes Refl) => ConMatch prf
                            _ => NoMatch
checkGroupMatch (CName x tag) ps (ConstGroup _ xs) = NoMatch
checkGroupMatch (CConst x) ps (ConGroup _ _ xs) = NoMatch
checkGroupMatch (CConst c) [] (ConstGroup c' (MkPatClause pats rhs :: rest)) 
    = case constantEq c c' of
           Nothing => NoMatch
           Just Refl => ConstMatch
checkGroupMatch _ _ _ = NoMatch

nextName : String -> StateT Int (Either CaseError) Name
nextName root
    = do i <- get
         put (i + 1)
         pure (MN root i)

nextNames : String -> List Pat -> Maybe (NF vars) ->
            StateT Int (Either CaseError) (args ** NamedPats (args ++ vars) args)
nextNames root [] fty = pure ([] ** [])
nextNames {vars} root (p :: pats) fty
     = do n <- nextName root
          let env = mkEnv vars
          let fa_tys : (Maybe (NF vars), ArgType vars)
                  = case fty of
                         Nothing => (Nothing, Unknown)
                         Just (NBind _ (Pi c _ farg) fsc) =>
                            (Just (fsc (toClosure False env (Ref Bound n))),
                              Known c (quote initCtxt env farg))
                         Just t =>
                            (Nothing, Stuck (quote initCtxt env t))
          (args ** ps) <- nextNames {vars} root pats
                               (fst fa_tys)
          let argTy = case snd fa_tys of
                           Unknown => Unknown
                           Known rig t => Known rig (weakenNs (n :: args) t)
                           Stuck t => Stuck (weakenNs (n :: args) t)
          pure (n :: args ** MkInfo p Here argTy :: weaken ps)

-- replace the prefix of patterns with 'pargs'
newPats : (pargs : List Pat) -> LengthMatch pargs ns ->
          NamedPats vars (ns ++ todo) ->
          NamedPats vars ns 
newPats [] NilMatch rest = []
newPats (newpat :: xs) (ConsMatch w) (pi :: rest) 
  = record { pat = newpat} pi :: newPats xs w rest

substPatNames : (ns : _) -> NamedPats vars ns -> Term vars -> Term vars
substPatNames [] [] tm = tm
substPatNames (n :: ns) (MkInfo (PVar pn) _ _ :: ps) tm 
     = substName pn (Ref Bound n) (substPatNames ns ps tm)
substPatNames (n :: ns) (_ :: ps) tm = substPatNames ns ps tm

updateNames : List (Name, Pat) -> List (Name, Name)
updateNames = mapMaybe update
  where
    update : (Name, Pat) -> Maybe (Name, Name)
    update (n, PVar p) = Just (p, n)
    update _ = Nothing

updatePatNames : List (Name, Name) -> NamedPats vars todo -> NamedPats vars todo
updatePatNames _ [] = []
updatePatNames ns (pi :: ps)
    = record { pat $= update } pi :: updatePatNames ns ps
  where
    update : Pat -> Pat
    update (PCon n i ps) = PCon n i (map update ps)
    update (PTCon n i ps) = PTCon n i (map update ps)
    update (PVar n) = case lookup n ns of
                           Nothing => PVar n
                           Just n' => PVar n'
    update p = p

groupCons : Defs ->
            List (PatClause vars (a :: todo)) -> 
            StateT Int (Either CaseError) (List (Group vars todo))
groupCons defs cs 
     = gc [] cs
  where
    addConG : Name -> (tag : Int) -> List Pat -> NamedPats vars todo ->
              (rhs : Term vars) ->
              (acc : List (Group vars todo)) ->
              StateT Int (Either CaseError) (List (Group vars todo))
    -- Group all the clauses that begin with the same constructor, and
    -- add new pattern arguments for each of that constructor's arguments.
    -- The type of 'ConGroup' ensures that we refer to the arguments by
    -- the same name in each of the clauses
    addConG {todo} n tag pargs pats rhs [] 
        = do let cty = case lookupTyExact n (gamma defs) of
                            Just t => nf defs (mkEnv vars) (embed t)
                            _ => NErased
             (patnames ** newargs) <- nextNames {vars} "e" pargs (Just cty)
             -- Update non-linear names in remaining patterns (to keep
             -- explicit dependencies in types accurate)
             let pats' = updatePatNames (updateNames (zip patnames pargs))
                                        (weakenNs patnames pats)
             let clause = MkPatClause {todo = patnames ++ todo} 
                              (newargs ++ pats') 
                              (weakenNs patnames rhs)
             pure [ConGroup n tag [clause]]
    addConG {todo} n tag pargs pats rhs (g :: gs) with (checkGroupMatch (CName n tag) pargs g)
      addConG {todo} n tag pargs pats rhs
              ((ConGroup {newargs} n tag ((MkPatClause ps tm) :: rest)) :: gs)
                   | (ConMatch {newargs} lprf) 
        = do let newps = newPats pargs lprf ps
             let pats' = updatePatNames (updateNames (zip newargs pargs))
                                        (weakenNs newargs pats)
             let newclause : PatClause (newargs ++ vars) (newargs ++ todo)
                   = MkPatClause (newps ++ pats')
                                 (weakenNs newargs rhs)
             -- put the new clause at the end of the group, since we
             -- match the clauses top to bottom.
             pure ((ConGroup n tag (MkPatClause ps tm :: rest ++ [newclause]))
                         :: gs)
      addConG n tag pargs pats rhs (g :: gs) | NoMatch 
        = do gs' <- addConG n tag pargs pats rhs gs
             pure (g :: gs')

    addConstG : Constant -> NamedPats vars todo ->
                (rhs : Term vars) ->
                (acc : List (Group vars todo)) ->
                StateT Int (Either CaseError) (List (Group vars todo))
    addConstG c pats rhs [] 
        = pure [ConstGroup c [MkPatClause pats rhs]]
    addConstG {todo} c pats rhs (g :: gs) with (checkGroupMatch (CConst c) [] g)
      addConstG {todo} c pats rhs
              ((ConstGroup c ((MkPatClause ps tm) :: rest)) :: gs) | ConstMatch                    
          = let newclause : PatClause vars todo
                  = MkPatClause pats rhs in
                pure ((ConstGroup c 
                      (MkPatClause ps tm :: rest ++ [newclause])) :: gs)
      addConstG c pats rhs (g :: gs) | NoMatch 
          = do gs' <- addConstG c pats rhs gs
               pure (g :: gs')
 
    addGroup : Pat -> NamedPats vars todo -> Term vars -> 
               List (Group vars todo) -> 
               StateT Int (Either CaseError) (List (Group vars todo))
    addGroup (PCon n t pargs) pats rhs acc 
        -- Erase forced arguments here
--         = do let pargs' = case lookupDefExact n (gamma defs) of
--                                Just (DCon _ _ f) => dropForced 0 f pargs
--                                _ => pargs
         = addConG n t pargs pats rhs acc
      where
        dropForced : Nat -> List Nat -> List Pat -> List Pat
        dropForced i fs [] = []
        dropForced i fs (x :: xs)
            = if i `elem` fs then PAny :: dropForced (S i) fs xs
                             else x :: dropForced (S i) fs xs
    addGroup (PConst c) pats rhs acc 
        = addConstG c pats rhs acc
    addGroup _ pats rhs acc = pure acc -- Can't happen, not a constructor
        -- FIXME: Is this possible to rule out with a type? Probably.

    gc : List (Group vars todo) -> 
         List (PatClause vars (a :: todo)) -> 
         StateT Int (Either CaseError) (List (Group vars todo))
    gc acc [] = pure acc
    gc {a} acc ((MkPatClause (MkInfo pat pprf fty :: pats) rhs) :: cs) 
        = do acc' <- addGroup pat pats rhs acc
             gc acc' cs

getFirstPat : NamedPats ns (p :: ps) -> Pat
getFirstPat (p :: _) = pat p

getFirstArgType : NamedPats ns (p :: ps) -> ArgType ns
getFirstArgType (p :: _) = argType p

-- Check whether all the initial patterns have the same concrete, known
-- and matchable type, which is multiplicity > 0. 
-- If so, it's okay to match on it
sameType : Defs -> Env Term ns -> List (NamedPats ns (p :: ps)) -> Bool
sameType defs env [] = True
sameType {ns} defs env (p :: xs) = -- all known (map getFirstArgType (p :: xs)) &&
    case getFirstArgType p of
         Known _ t => sameTypeAs (nf defs env t) (map getFirstArgType xs)
         _ => False
  where
    headEq : NF ns -> NF ns -> Bool
    headEq (NTCon n _ _ _) (NTCon n' _ _ _) = n == n'
    headEq (NPrimVal c) (NPrimVal c') = c == c'
    headEq _ _ = False

    sameTypeAs : NF ns -> List (ArgType ns) -> Bool
    sameTypeAs ty [] = True
    sameTypeAs ty (Known Rig0 t :: xs) = False -- Can't match on erased thing
    sameTypeAs ty (Known c t :: xs) 
          = headEq ty (nf defs env t) && sameTypeAs ty xs
    sameTypeAs ty _ = False

-- Check whether all the initial patterns are the same, or are all a variable.
-- If so, we'll match it to refine later types and move on
samePat : List (NamedPats ns (p :: ps)) -> Bool
samePat [] = True
samePat (pi :: xs) = samePatAs (getFirstPat pi) (map getFirstPat xs)
  where
    samePatAs : Pat -> List Pat -> Bool
    samePatAs p [] = True
    samePatAs (PTCon n t args) (PTCon n' t' _ :: ps)
        = if n == n' && t == t'
             then samePatAs (PTCon n t args) ps
             else False
    samePatAs (PCon n t args) (PCon n' t' _ :: ps)
        = if n == n' && t == t'
             then samePatAs (PCon n t args) ps
             else False
    samePatAs (PConstTy c) (PConstTy c' :: ps)
        = if c == c' 
             then samePatAs (PConstTy c) ps
             else False
    samePatAs (PConst c) (PConst c' :: ps)
        = if c == c' 
             then samePatAs (PConst c) ps
             else False
    samePatAs (PVar n) (PVar _ :: ps) = samePatAs (PVar n) ps
    samePatAs x y = False

getFirstCon : NamedPats ns (p :: ps) -> Pat
getFirstCon (p :: _) = pat p

-- Count the number of distinct constructors in the initial pattern
countDiff : List (NamedPats ns (p :: ps)) -> Nat
countDiff xs = length (distinct [] (map getFirstCon xs))
  where
    isVar : Pat -> Bool
    isVar (PCon _ _ _) = False
    isVar (PConst _) = False
    isVar _ = True

    -- Return whether two patterns would lead to the same match
    sameCase : Pat -> Pat -> Bool
    sameCase (PCon _ t _) (PCon _ t' _) = t == t'
    sameCase (PConst c) (PConst c') = c == c'
    sameCase x y = isVar x && isVar y

    distinct : List Pat -> List Pat -> List Pat
    distinct acc [] = acc
    distinct acc (p :: ps) 
       = if elemBy sameCase p acc 
            then distinct acc ps
            else distinct (p :: acc) ps

getScore : Defs -> Elem x (p :: ps) -> 
           List (NamedPats ns (p :: ps)) -> Maybe (Elem x (p :: ps), Nat)
getScore defs prf npss 
    = if sameType defs (mkEnv ns) npss
         then Just (prf, countDiff npss)
         else Nothing

bestOf : Maybe (Elem p ps, Nat) -> Maybe (Elem q ps, Nat) ->
         Maybe (x ** (Elem x ps, Nat))
bestOf Nothing Nothing = Nothing
bestOf Nothing (Just p) = Just (_ ** p)
bestOf (Just p) Nothing = Just (_ ** p)
bestOf (Just (p, psc)) (Just (q, qsc))
    = Just (_ ** (p, psc))
         -- at compile time, left to right helps coverage check
         -- (by refining types, so we know the type of the thing we're
         -- discriminating on)
         -- TODO: At run time pick most distinct, as below?
--     if psc >= qsc
--          then Just (_ ** (p, psc))
--          else Just (_ ** (q, qsc))

pickBest : Defs -> List (NamedPats ns (p :: ps)) -> 
           Maybe (x ** (Elem x (p :: ps), Nat))
pickBest {ps = []} defs npss 
    = if samePat npss
         then pure (_ ** (Here, 0))
         else do el <- getScore defs Here npss
                 pure (_ ** el)
pickBest {ps = q :: qs} defs npss 
    = -- Pick the leftmost thing with all constructors in the same family,
      -- or all variables, or all the same type constructor
      if samePat npss
         then pure (_ ** (Here, 0))
         else
            case pickBest defs (map tail npss) of
                 Nothing => 
                    do el <- getScore defs Here npss
                       pure (_ ** el)
                 Just (_ ** (var, score)) =>
                    bestOf (getScore defs Here npss) (Just (There var, score))

-- Pick the next variable to inspect from the list of LHSs.
-- Choice *must* be the same type family, so pick the leftmost argument
-- where this applies.
pickNext : Defs -> List (NamedPats ns (p :: ps)) -> 
           Maybe (x ** Elem x (p :: ps))
pickNext defs npss 
   = case pickBest defs npss of
          Nothing => Nothing
          Just (_ ** (best, _)) => Just (_ ** best)

moveFirst : (el : Elem x ps) -> NamedPats ns ps ->
            NamedPats ns (x :: dropElem ps el)
moveFirst el nps = getPat el nps :: dropPat el nps

shuffleVars : (el : Elem x todo) -> PatClause vars todo ->
              PatClause vars (x :: dropElem todo el)
shuffleVars el (MkPatClause lhs rhs) = MkPatClause (moveFirst el lhs) rhs

{- 'match' does the work of converting a group of pattern clauses into
   a case tree, given a default case if none of the clauses match -}

mutual
  {- 'PatClause' contains a list of patterns still to process (that's the 
     "todo") and a right hand side with the variables we know about "vars".
     So "match" builds the remainder of the case tree for
     the unprocessed patterns. "err" is the tree for when the patterns don't
     cover the input (i.e. the "fallthrough" pattern, which at the top
     level will be an error). -}
  match : Defs -> List (PatClause vars todo) -> (err : Maybe (CaseTree vars)) -> 
               StateT Int (Either CaseError) (CaseTree vars)
  -- Before 'partition', reorder the arguments so that the one we
  -- inspect next has a concrete type that is the same in all cases, and
  -- has the most distinct constructors (via pickNext)
  match {todo = (_ :: _)} defs clauses err 
      = case pickNext defs (map getNPs clauses) of
             Nothing => lift $ Left DifferingTypes
             Just (_ ** next) =>
                let clauses' = map (shuffleVars next) clauses
                    ps = partition clauses' in
                    maybe (pure (Unmatched "No clauses"))
                          pure
                          !(mixture defs ps err)
  match {todo = []} defs [] err 
       = maybe (pure (Unmatched "No patterns"))
               pure err
  match {todo = []} defs ((MkPatClause [] rhs) :: _) err 
       = pure $ STerm rhs

  caseGroups : Defs ->
               Elem pvar vars -> Term vars ->
               List (Group vars todo) -> Maybe (CaseTree vars) ->
               StateT Int (Either CaseError) (CaseTree vars)
  caseGroups {vars} defs el ty gs errorCase
      = do g <- altGroups gs
           pure (Case el (resolveRefs vars ty) g)
    where
      altGroups : List (Group vars todo) -> 
                  StateT Int (Either CaseError) (List (CaseAlt vars))
      altGroups [] = maybe (pure []) 
                           (\e => pure [DefaultCase e]) 
                           errorCase
      altGroups (ConGroup {newargs} cn tag rest :: cs) 
          = do crest <- match defs rest (map (weakenNs newargs) errorCase)
               cs' <- altGroups cs
               pure (ConCase cn tag newargs crest :: cs')
      altGroups (ConstGroup c rest :: cs)
          = do crest <- match defs rest errorCase
               cs' <- altGroups cs
               pure (ConstCase c crest :: cs')

  conRule : Defs ->
            List (PatClause vars (a :: todo)) ->
            Maybe (CaseTree vars) -> 
            StateT Int (Either CaseError) (CaseTree vars)
  conRule defs [] err = maybe (pure (Unmatched "No constructor clauses")) pure err 
  -- ASSUMPTION, not expressed in the type, that the patterns all have
  -- the same variable (pprf) for the first argument. If not, the result
  -- will be a broken case tree... so we should find a way to express this
  -- in the type if we can.
  conRule {a} defs cs@(MkPatClause (MkInfo pat pprf fty :: pats) rhs :: rest) err 
      = do let refinedcs = map (substInClause defs) cs
           groups <- groupCons defs refinedcs
           ty <- case fty of
                      Known _ t => pure t
                      _ => lift $ Left UnknownType
           caseGroups defs pprf ty groups err

  varRule : Defs ->
            List (PatClause vars (a :: todo)) ->
            Maybe (CaseTree vars) -> 
            StateT Int (Either CaseError) (CaseTree vars)
  varRule {vars} {a} defs cs err 
      = do let alts' = map updateVar cs
           match defs alts' err
    where
      updateVar : PatClause vars (a :: todo) -> PatClause vars todo
      -- replace the name with the relevant variable on the rhs
      updateVar (MkPatClause (MkInfo (PVar n) prf fty :: pats) rhs)
          = MkPatClause (substInPats defs a (Local prf) pats)
                        (substName n (Local prf) rhs) 
      -- match anything, name won't appear in rhs but need to update
      -- LHS pattern types based on what we've learned
      updateVar (MkPatClause (MkInfo pat prf fty :: pats) rhs)
          = MkPatClause (substInPats defs a (mkTerm vars pat) pats) rhs

  mixture : {ps : List (PatClause vars (a :: todo))} ->
            Defs ->
            Partitions ps -> 
            Maybe (CaseTree vars) -> 
            StateT Int (Either CaseError) (Maybe (CaseTree vars))
  mixture defs (ConClauses cs rest) err 
      = do fallthrough <- mixture defs rest err
           pure (Just !(conRule defs cs fallthrough))
  mixture defs (VarClauses vs rest) err 
      = do fallthrough <- mixture defs rest err
           pure (Just !(varRule defs vs fallthrough))
  mixture defs {a} {todo} NoClauses err 
      = pure err

mkPatClause : Defs ->
              (args : List Name) -> ClosedTerm -> (List Pat, ClosedTerm) ->
              Either CaseError (PatClause args args)
mkPatClause defs args ty (ps, rhs) 
    = maybe (Left DifferingArgNumbers)
            (\eq => 
               let nty = nf defs [] ty in
                 Right (MkPatClause (mkNames args ps eq (Just nty))
                    (rewrite sym (appendNilRightNeutral args) in 
                             (weakenNs args rhs))))
            (checkLengthMatch args ps)
  where
    mkNames : (vars : List Name) -> (ps : List Pat) -> 
              LengthMatch vars ps -> Maybe (NF []) ->
              NamedPats vars vars
    mkNames [] [] NilMatch fty = []
    mkNames (arg :: args) (p :: ps) (ConsMatch eq) fty
        = let fa_tys = case fty of
                            Nothing => (Nothing, Unknown)
                            Just (NBind _ (Pi c _ farg) fsc) => 
                                (Just (fsc (toClosure False [] (Ref Bound arg))),
                                   Known c (embed {more = arg :: args} 
                                             (quote initCtxt [] farg)))
                            Just t => 
                                (Nothing, 
                                   Stuck (embed {more = arg :: args} 
                                             (quote initCtxt [] t))) in
              MkInfo p Here (snd fa_tys)
                    :: weaken (mkNames args ps eq 
                             (fst fa_tys)) 

export
patCompile : Defs -> 
             ClosedTerm -> List (List Pat, ClosedTerm) -> 
             Maybe (CaseTree []) ->
             Either CaseError (args ** CaseTree args)
patCompile defs ty [] def 
    = maybe (pure ([] ** Unmatched "No definition"))
            (\e => pure ([] ** e))
            def
patCompile defs ty (p :: ps) def 
    = do let ns = getNames 0 (fst p)
         pats <- traverse (mkPatClause defs ns ty) (p :: ps)
         (cases, _) <- runStateT (match defs pats 
                                    (rewrite sym (appendNilRightNeutral ns) in
                                             map (weakenNs ns) def)) 0
         pure (_ ** cases)
  where
    getNames : Int -> List Pat -> List Name
    getNames i [] = []
    getNames i (x :: xs) = MN "arg" i :: getNames (i + 1) xs

toPatClause : annot -> Name -> (ClosedTerm, ClosedTerm) ->
              Core annot (List Pat, ClosedTerm)
toPatClause loc n (lhs, rhs) with (unapply lhs)
  toPatClause loc n (apply (Ref Func fn) args, rhs) | ArgsList 
      = case nameEq n fn of
             Nothing => throw (GenericMsg loc ("Wrong function name in pattern LHS " ++ show (n, fn)))
             Just Refl => do -- putStrLn $ "Clause: " ++ show (apply (Ref Func fn) args) ++ " = " ++ show rhs
                             pure (map argToPat args, rhs)
  toPatClause loc n (apply f args, rhs) | ArgsList 
      = throw (GenericMsg loc "Not a function name in pattern LHS")


-- Assumption (given 'ClosedTerm') is that the pattern variables are
-- explicitly named. We'll assign de Bruijn indices when we're done, and
-- the names of the top level variables we created are returned in 'args'
export
simpleCase : {auto x : Ref Ctxt Defs} ->
             annot -> Name -> ClosedTerm -> (def : Maybe (CaseTree [])) ->
             (clauses : List (ClosedTerm, ClosedTerm)) ->
             Core annot (args ** CaseTree args)
simpleCase loc fn ty def clauses 
    = do ps <- traverse (toPatClause loc fn) clauses
         defs <- get Ctxt
         case patCompile defs ty ps def of
              Left err => throw (CaseCompile loc fn err)
              Right ok => pure ok

export
getPMDef : {auto x : Ref Ctxt Defs} ->
           annot -> Name -> ClosedTerm -> List Clause -> 
           Core annot (args ** CaseTree args)
getPMDef loc fn ty clauses
    = let cs = map toClosed clauses in
          simpleCase loc fn ty Nothing cs
  where
    close : Int -> (plets : Bool) -> Env Term vars -> Term vars -> ClosedTerm
    close i plets [] tm = tm
    close i True (PLet c val ty :: bs) tm 
		    = close (i + 1) True bs (Bind (MN "pat" i) (Let c val ty) (renameTop _ tm))
    close i True (Let c val ty :: bs) tm 
		    = close (i + 1) True bs (Bind (MN "pat" i) (Let c val ty) (renameTop _ tm))
    close i plets (b :: bs) tm 
        = close (i + 1) plets bs (subst (Ref Bound (MN "pat" i)) tm)

    toClosed : Clause -> (ClosedTerm, ClosedTerm)
    toClosed (MkClause env lhs rhs) 
          = (close 0 False env lhs, close 0 True env rhs)

