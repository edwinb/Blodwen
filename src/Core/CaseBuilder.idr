module Core.CaseBuilder

import public Core.CaseTree
import Core.TT

import Control.Monad.State
import Data.List

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
     (::) : (Pat, Elem pvar vars) -> -- a pattern, and where its variable appears in the vars list
            NamedPats vars ns -> NamedPats vars (pvar :: ns)

Show (NamedPats vars todo) where
  show xs = "[" ++ showAll xs ++ "]"
    where
      showAll : NamedPats vs ts -> String
      showAll [] = ""
      showAll [x] = show (fst x)
      showAll (x :: xs) = show (fst x) ++ ", " ++ showAll xs

-- FIXME: oops, 'vars' should be second argument so we can use Weaken interface
weaken : NamedPats vars todo -> NamedPats (x :: vars) todo
weaken [] = []
weaken ((p, el) :: ps) = (p, There el) :: weaken ps

weakenNs : (ns : List Name) -> 
           NamedPats vars todo -> NamedPats (ns ++ vars) todo
weakenNs ns [] = []
weakenNs ns ((p, el) :: ps) = (p, weakenElem el) :: weakenNs ns ps

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

Show (PatClause vars todo) where
  show (MkPatClause ps rhs) = show ps ++ " => " ++ show rhs

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
clauseType (MkPatClause ((PVar x, _) :: _) rhs) = VarClause
clauseType (MkPatClause ((PAny, _) :: _) rhs) = VarClause

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

nextName : String -> State Int Name
nextName root
    = do i <- get
         put (i + 1)
         pure (MN root i)

nextNames : String -> List Pat -> 
            State Int (args ** NamedPats (args ++ vars) args)
nextNames root [] = pure ([] ** [])
nextNames {vars} root (p :: pats) 
     = do (args ** ps) <- nextNames {vars} root pats
          n <- nextName root
          pure (n :: args ** (p, Here) :: weaken ps)

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

groupCons : List (PatClause vars (a :: todo)) -> 
            State Int (List (Group vars todo))
groupCons cs 
     = gc [] cs
  where
    addConG : Name -> (tag : Int) -> List Pat -> NamedPats vars todo ->
              (rhs : Term vars) ->
              (acc : List (Group vars todo)) ->
              State Int (List (Group vars todo))
    -- Group all the clauses that begin with the same constructor, and
    -- add new pattern arguments for each of that constructor's arguments.
    -- The type of 'ConGroup' ensures that we refer to the arguments by
    -- the same name in each of the clauses
    addConG {todo} n tag pargs pats rhs [] 
        = do (patnames ** newargs) <- nextNames {vars} "e" pargs
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
                State Int (List (Group vars todo))
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
               State Int (List (Group vars todo))
    addGroup (PCon n t pargs) pats rhs acc 
        = addConG n t pargs pats rhs acc
    addGroup (PConst c) pats rhs acc 
        = addConstG c pats rhs acc
    addGroup _ pats rhs acc = pure acc -- Can't happen, not a constructor
        -- FIXME: Is this possible to rule out with a type? Probably.

    gc : List (Group vars todo) -> 
         List (PatClause vars (a :: todo)) -> 
         State Int (List (Group vars todo))
    gc acc [] = pure acc
    gc {a} acc ((MkPatClause ((pat, pprf) :: pats) rhs) :: cs) 
        = do acc' <- addGroup pat pats rhs acc
             gc acc' cs

{- 'match' does the work of converting a group of pattern clauses into
   a case tree, given a default case if none of the clauses match -}

mutual
  {- 'PatClause' contains a list of patterns still to process (that's the 
     "todo") and a right hand side with the variables we know about "vars".
     So "match" builds the remainder of the case tree for
     the unprocessed patterns. "err" is the tree for when the patterns don't
     cover the input (i.e. the "fallthrough" pattern, which at the top
     level will be an error). -}
  match : List (PatClause vars todo) -> (err : CaseTree vars) -> 
               State Int (CaseTree vars)
  match {todo = []} [] err = pure err
  match {todo = []} ((MkPatClause [] rhs) :: _) err 
       = pure $ STerm rhs
  match {todo = (_ :: _)} clauses err 
      = let ps = partition clauses in
            mixture (partition clauses) err

  caseGroups : Elem pvar vars ->
               List (Group vars todo) -> CaseTree vars ->
               State Int (CaseTree vars)
  caseGroups {vars} el gs errorCase
      = do g <- altGroups gs
           pure (Case el g)
    where
      altGroups : List (Group vars todo) -> 
                  State Int (List (CaseAlt vars))
      altGroups [] = pure [DefaultCase errorCase]
      altGroups (ConGroup {newargs} cn tag rest :: cs) 
          = do crest <- assert_total $ match rest (weakenNs newargs errorCase)
               cs' <- altGroups cs
               pure (ConCase cn tag newargs crest :: cs')
      altGroups (ConstGroup c rest :: cs)
          = do crest <- assert_total $ match rest errorCase
               cs' <- altGroups cs
               pure (ConstCase c crest :: cs')

  conRule : List (PatClause vars (a :: todo)) -> 
            CaseTree vars -> 
            State Int (CaseTree vars)
  conRule [] err = pure err 
  -- TODO, ASSUMPTION, not expressed in the type, that the patterns all have
  -- the same variable (pprf) for the first argument. If not, the result
  -- will be a broken case tree... so we should find a way to express this
  -- in the type.
  conRule cs@(MkPatClause ((pat, pprf) :: pats) rhs :: rest) err 
      = do groups <- groupCons cs
           caseGroups pprf groups err

  varRule : List (PatClause vars (a :: todo)) -> 
            CaseTree vars -> 
            State Int (CaseTree vars)
  varRule cs err 
      = do let alts' = map updateVar cs
           match alts' err
    where
      updateVar : PatClause vars (a :: todo) -> PatClause vars todo
      -- replace the name with the relevant variable on the rhs
      updateVar (MkPatClause ((PVar n, prf) :: pats) rhs)
          = MkPatClause pats (substName n (Local prf) rhs)
      -- match anything, name won't appear in rhs
      updateVar (MkPatClause ((p, _) :: pats) rhs)
          = MkPatClause pats rhs

  mixture : {ps : List (PatClause vars (a :: todo))} ->
            Partitions ps -> CaseTree vars -> 
            State Int (CaseTree vars)
  mixture (ConClauses cs rest) err 
      = do fallthrough <- mixture rest err
           conRule cs fallthrough
  mixture (VarClauses vs rest) err 
      = do fallthrough <- mixture rest err
           varRule vs fallthrough
  mixture {a} {todo} NoClauses err = pure err

mkPatClause : (args : List Name) -> (List Pat, ClosedTerm) ->
              Either CaseError (PatClause args args)
mkPatClause args (ps, rhs) 
    = case checkLengthMatch args ps of
           Nothing => Left DifferingArgNumbers
           Just eq => 
               Right (MkPatClause (mkNames args ps eq) 
                  (rewrite sym (appendNilRightNeutral args) in 
                           (weakenNs args rhs)))
  where
    mkNames : (vars : List Name) -> (ps : List Pat) -> 
              LengthMatch vars ps -> 
              NamedPats vars vars
    mkNames [] [] NilMatch = []
    mkNames (arg :: args) (p :: ps) (ConsMatch eq)
        = (p, Here) :: weaken (mkNames args ps eq) 

export
patCompile : List (List Pat, ClosedTerm) -> CaseTree [] ->
             Either CaseError (args ** CaseTree args)
patCompile [] def = pure ([] ** def)
patCompile (p :: ps) def 
    = do let ns = getNames 0 (fst p)
         pats <- traverse (mkPatClause ns) (p :: ps)
         let cases = evalState (match pats 
                                  (rewrite sym (appendNilRightNeutral ns) in
                                           weakenNs ns def)) 0
         pure (_ ** cases)
  where
    getNames : Int -> List Pat -> List Name
    getNames i [] = []
    getNames i (x :: xs) = MN "arg" i :: getNames (i + 1) xs

