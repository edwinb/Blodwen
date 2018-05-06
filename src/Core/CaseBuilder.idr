module Core.CaseBuilder

import public Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT

import Control.Monad.State
import Data.List

import Debug.Trace

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
     (::) : (Pat, Elem pvar vars, NF []) -> 
            -- ^ a pattern, where its variable appears in the vars list,
            -- and its type. The type has no variable names; any names it
            -- refers to are explicit
            NamedPats vars ns -> NamedPats vars (pvar :: ns)

getPat : Elem x ps -> NamedPats ns ps -> (Pat, Elem x ns, NF [])
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
      showAll [x]
          = show (fst x) ++ " : " ++ show (quote initCtxt [] (snd (snd x)))
      showAll (x :: xs) 
          = show (fst x) ++ " : " ++ show (quote initCtxt [] (snd (snd x)))
                 ++ ", " ++ showAll xs

-- FIXME: oops, 'vars' should be second argument so we can use Weaken interface
weaken : NamedPats vars todo -> NamedPats (x :: vars) todo
weaken [] = []
weaken ((p, el, ty) :: ps) = (p, There el, ty) :: weaken ps

weakenNs : (ns : List Name) -> 
           NamedPats vars todo -> NamedPats (ns ++ vars) todo
weakenNs ns [] = []
weakenNs ns ((p, el, ty) :: ps) 
    = (p, weakenElem el, ty) :: weakenNs ns ps

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
clauseType (MkPatClause ((PCon x y xs, _) :: _) rhs) = ConClause
clauseType (MkPatClause ((PConst x, _) :: _) rhs) = ConClause
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

nextNames : String -> List Pat -> NF [] ->
            StateT Int (Either CaseError) (args ** NamedPats (args ++ vars) args)
nextNames root [] ty = pure ([] ** [])
nextNames {vars} root (p :: pats) (NBind _ (Pi _ _ pty) sc)
     = do (args ** ps) <- nextNames {vars} root pats
                               (sc (toClosure False [] (mkTerm p)))
          n <- nextName root 
          pure (n :: args ** (p, Here, pty) :: weaken ps)
-- This case should probably give an error...
nextNames {vars} root (p :: pats) _
     = do (args ** ps) <- nextNames {vars} root pats NErased
          n <- nextName root
          trace ("This shouldn't happen (2) CaseBuilder.idr") $
            pure (n :: args ** (p, Here, NErased) :: weaken ps)

-- replace the prefix of patterns with 'pargs'
newPats : (pargs : List Pat) -> LengthMatch pargs ns ->
          NamedPats vars (ns ++ todo) ->
          NamedPats vars ns 
newPats [] NilMatch rest = []
newPats (newpat :: xs) (ConsMatch w) ((pat, pprf) :: rest) 
  = (newpat, pprf) :: newPats xs w rest

substPatNames : (ns : _) -> NamedPats vars ns -> Term vars -> Term vars
substPatNames [] [] tm = tm
substPatNames (n :: ns) ((PVar pn, _) :: ps) tm 
     = substName pn (Ref Bound n) (substPatNames ns ps tm)
substPatNames (n :: ns) (_ :: ps) tm = substPatNames ns ps tm

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
                            Just t => nf defs [] t
                            _ => NErased
             (patnames ** newargs) <- nextNames {vars} "e" pargs cty
             pure [ConGroup n tag
               [MkPatClause {todo = patnames ++ todo} 
                  (newargs ++ weakenNs patnames pats) 
                  (weakenNs patnames rhs)]]
    addConG {todo} n tag pargs pats rhs (g :: gs) with (checkGroupMatch (CName n tag) pargs g)
      addConG {todo} n tag pargs pats rhs
              ((ConGroup {newargs} n tag ((MkPatClause ps tm) :: rest)) :: gs)
                   | (ConMatch {newargs} lprf) 
        = do let newps = newPats pargs lprf ps
             let newclause : PatClause (newargs ++ vars) (newargs ++ todo)
                   = MkPatClause (newps ++ weakenNs newargs pats)
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
        = do let pargs' = case lookupDefExact n (gamma defs) of
                               Just (DCon _ _ f) => dropForced 0 f pargs
                               _ => pargs
             addConG n t pargs' pats rhs acc
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
    gc {a} acc ((MkPatClause ((pat, pprf, pty) :: pats) rhs) :: cs) 
        = do acc' <- addGroup pat pats rhs acc
             gc acc' cs

getFirstType : NamedPats ns (p :: ps) -> NF []
getFirstType ((_, _, ty) :: _) = ty

-- Check whether all the initial patterns have the same concrete type. If so,
-- it's okay to match on it
sameType : List (NamedPats ns (p :: ps)) -> Bool
sameType [] = True
sameType (p :: xs) = sameTypeAs (getFirstType p) (map getFirstType xs)
  where
    headEq : NF [] -> NF [] -> Bool
    headEq (NTCon n _ _ _) (NTCon n' _ _ _) = n == n'
    headEq (NPrimVal c) (NPrimVal c') = c == c'
    headEq NType NType = True
    headEq _ _ = False

    sameTypeAs : NF [] -> List (NF []) -> Bool
    sameTypeAs ty [] = True
    sameTypeAs ty (x :: xs) = headEq ty x && sameTypeAs ty xs

getFirstCon : NamedPats ns (p :: ps) -> Pat
getFirstCon ((pat, _, _) :: _) = pat

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

getScore : Elem x (p :: ps) -> 
           List (NamedPats ns (p :: ps)) -> Maybe (Elem x (p :: ps), Nat)
getScore prf npss 
    = if sameType npss
         then Just (prf, countDiff npss)
         else Nothing

bestOf : Maybe (Elem p ps, Nat) -> Maybe (Elem q ps, Nat) ->
         Maybe (x ** (Elem x ps, Nat))
bestOf Nothing Nothing = Nothing
bestOf Nothing (Just p) = Just (_ ** p)
bestOf (Just p) Nothing = Just (_ ** p)
bestOf (Just (p, psc)) (Just (q, qsc))
    = if psc > qsc
         then Just (_ ** (p, psc))
         else Just (_ ** (q, qsc))

pickBest : List (NamedPats ns (p :: ps)) -> Maybe (x ** (Elem x (p :: ps), Nat))
pickBest {ps = []} npss 
    = do el <- getScore Here npss
         pure (_ ** el)
pickBest {ps = q :: qs} npss 
    = case pickBest (map tail npss) of
           Nothing => 
              do el <- getScore Here npss
                 pure (_ ** el)
           Just (_ ** (var, score)) =>
              bestOf (getScore Here npss) (Just (There var, score))

-- Pick the next variable to inspect from the list of LHSs.
-- Choice *must* be the same type family. Pick the one with most distinct
-- constructors as a heuristic to generate a smaller case tree
pickNext : List (NamedPats ns (p :: ps)) -> Maybe (x ** Elem x (p :: ps))
pickNext npss 
   = case pickBest npss of
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
  match : Defs -> List (PatClause vars todo) -> (err : CaseTree vars) -> 
               StateT Int (Either CaseError) (CaseTree vars)
  match {todo = []} defs [] err = pure err
  match {todo = []} defs ((MkPatClause [] rhs) :: _) err 
       = pure $ STerm rhs
  -- Before 'partition', reorder the arguments so that the one we
  -- inspect next has a concrete type that is the same in all cases, and
  -- has the most distinct constructors (via pickNext)
  match {todo = (_ :: _)} defs clauses err 
      = case pickNext (map getNPs clauses) of
             Nothing => lift $ Left DifferingTypes
             Just (_ ** next) =>
                let clauses' = map (shuffleVars next) clauses
                    ps = partition clauses' in
                    mixture defs (partition clauses') err

  caseGroups : Defs ->
               Elem pvar vars ->
               List (Group vars todo) -> CaseTree vars ->
               StateT Int (Either CaseError) (CaseTree vars)
  caseGroups {vars} defs el gs errorCase
      = do g <- altGroups gs
           pure (Case el g)
    where
      altGroups : List (Group vars todo) -> 
                  StateT Int (Either CaseError) (List (CaseAlt vars))
      altGroups [] = pure [DefaultCase errorCase]
      altGroups (ConGroup {newargs} cn tag rest :: cs) 
          = do crest <- assert_total $ match defs rest (weakenNs newargs errorCase)
               cs' <- altGroups cs
               pure (ConCase cn tag newargs crest :: cs')
      altGroups (ConstGroup c rest :: cs)
          = do crest <- assert_total $ match defs rest errorCase
               cs' <- altGroups cs
               pure (ConstCase c crest :: cs')

  conRule : Defs ->
            List (PatClause vars (a :: todo)) -> 
            CaseTree vars -> 
            StateT Int (Either CaseError) (CaseTree vars)
  conRule defs [] err = pure err 
  -- TODO, ASSUMPTION, not expressed in the type, that the patterns all have
  -- the same variable (pprf) for the first argument. If not, the result
  -- will be a broken case tree... so we should find a way to express this
  -- in the type.
  conRule defs cs@(MkPatClause ((pat, pprf, pty) :: pats) rhs :: rest) err 
      = do groups <- groupCons defs cs
           caseGroups defs pprf groups err

  varRule : Defs ->
            List (PatClause vars (a :: todo)) -> 
            CaseTree vars -> 
            StateT Int (Either CaseError) (CaseTree vars)
  varRule defs cs err 
      = do let alts' = map updateVar cs
           match defs alts' err
    where
      updateVar : PatClause vars (a :: todo) -> PatClause vars todo
      -- replace the name with the relevant variable on the rhs
      updateVar (MkPatClause ((PVar n, prf, pty) :: pats) rhs)
          = MkPatClause pats (substName n (Local prf) rhs) 
      -- match anything, name won't appear in rhs
      updateVar (MkPatClause ((p, _, _) :: pats) rhs)
          = MkPatClause pats rhs

  mixture : {ps : List (PatClause vars (a :: todo))} ->
            Defs ->
            Partitions ps -> CaseTree vars -> 
            StateT Int (Either CaseError) (CaseTree vars)
  mixture defs (ConClauses cs rest) err 
      = do fallthrough <- mixture defs rest err
           conRule defs cs fallthrough
  mixture defs (VarClauses vs rest) err 
      = do fallthrough <- mixture defs rest err
           varRule defs vs fallthrough
  mixture defs {a} {todo} NoClauses err = pure err

mkPatClause : Defs ->
              (args : List Name) -> ClosedTerm -> (List Pat, ClosedTerm) ->
              Either CaseError (PatClause args args)
mkPatClause defs args ty (ps, rhs) 
    = case checkLengthMatch args ps of
           Nothing => Left DifferingArgNumbers
           Just eq => 
               Right (MkPatClause (mkNames args ps eq (nf defs [] ty)) 
                  (rewrite sym (appendNilRightNeutral args) in 
                           (weakenNs args rhs)))
  where
    mkNames : (vars : List Name) -> (ps : List Pat) -> 
              LengthMatch vars ps -> NF [] ->
              NamedPats vars vars
    mkNames [] [] NilMatch ty = []
    mkNames (arg :: args) (p :: ps) (ConsMatch eq) (NBind _ (Pi _ _ pty) sc)
        = (p, Here, pty)
              :: weaken (mkNames args ps eq 
                       (sc (toClosure False [] (mkTerm p)))) 
    -- This case should probably give an error...
    mkNames (arg :: args) (p :: ps) (ConsMatch eq) _
        = trace ("This shouldn't happen (1) CaseBuilder.idr") $ 
            (p, Here, NErased) :: weaken (mkNames args ps eq NErased) 

export
patCompile : Defs -> 
             ClosedTerm -> List (List Pat, ClosedTerm) -> CaseTree [] ->
             Either CaseError (args ** CaseTree args)
patCompile defs ty [] def = pure ([] ** def)
patCompile defs ty (p :: ps) def 
    = do let ns = getNames 0 (fst p)
         pats <- traverse (mkPatClause defs ns ty) (p :: ps)
         (cases, _) <- runStateT (match defs pats 
                                    (rewrite sym (appendNilRightNeutral ns) in
                                             weakenNs ns def)) 0
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
             annot -> Name -> ClosedTerm -> (def : CaseTree []) ->
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
          simpleCase loc fn ty (Unmatched "Unmatched case") cs
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

