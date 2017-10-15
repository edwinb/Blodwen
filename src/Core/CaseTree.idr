module Core.CaseTree

import Core.TT

import Control.Monad.State -- TODO: Use StateE for consistency?
import Data.CSet
import Data.List

%default total

mutual
  public export
  data CaseTree : List Name -> Type where
       Case : Elem var vars -> List (CaseAlt vars) -> CaseTree vars
       STerm : Term vars -> CaseTree vars
       Unmatched : (msg : String) -> CaseTree vars
       Impossible : CaseTree vars

  %name CaseTree sc

  public export
  data CaseAlt : List Name -> Type where
       ConCase : Name -> (tag : Int) -> (args : List Name) ->
                 CaseTree (args ++ vars) -> CaseAlt vars
       ConstCase : Constant -> CaseTree vars -> CaseAlt vars
       DefaultCase : CaseTree vars -> CaseAlt vars
  
  %name CaseAlt alt

export
getRefs : CaseTree vars_in -> List Name
getRefs sc = CSet.toList (getSet empty sc)
  where
    mutual
      getAltSet : SortedSet -> CaseAlt vars -> SortedSet
      getAltSet ns (ConCase n t args sc) = getSet ns sc
      getAltSet ns (ConstCase i sc) = getSet ns sc
      getAltSet ns (DefaultCase sc) = getSet ns sc

      getAltSets : SortedSet -> List (CaseAlt vars) -> SortedSet
      getAltSets ns [] = ns
      getAltSets ns (a :: as) 
          = assert_total $ getAltSets (getAltSet ns a) as

      getSet : SortedSet -> CaseTree vars -> SortedSet
      getSet ns (Case x xs) = getAltSets ns xs
      getSet ns (STerm tm) = assert_total $ union ns (getRefs tm)
      getSet ns (Unmatched msg) = ns
      getSet ns Impossible = ns

mutual
  export
  Show (CaseTree vars) where
    show (Case {var} prf alts)
        = "case " ++ show var ++ " of { " ++
                     showSep "| " (assert_total (map show alts))
    show (STerm tm) = show tm
    show (Unmatched msg) = "Error: " ++ show msg
    show Impossible = "Impossible"

  export
  Show (CaseAlt vars) where
    show (ConCase n tag args sc)
        = show n ++ " " ++ showSep " " (map show args) ++ " => " ++
          show sc
    show (ConstCase c sc)
        = show c ++ " => " ++ show sc
    show (DefaultCase sc)
        = "_ => " ++ show sc

mutual
  insertCaseNames : (ns : List Name) -> CaseTree (outer ++ inner) ->
                    CaseTree (outer ++ (ns ++ inner))
  insertCaseNames {outer} {inner} ns (Case x xs) 
      = Case (insertElemNames {outer} {inner} ns x)
             (assert_total (map (insertCaseAltNames {outer} {inner} ns)) xs)
  insertCaseNames {outer} ns (STerm tm) = STerm (insertNames {outer} ns tm)
  insertCaseNames ns (Unmatched msg) = Unmatched msg
  insertCaseNames ns Impossible = Impossible

  insertCaseAltNames : (ns : List Name) -> CaseAlt (outer ++ inner) ->
                       CaseAlt (outer ++ (ns ++ inner))
  insertCaseAltNames {outer} {inner}  ns (ConCase x tag args sc) 
      = ConCase x tag args 
             (assert_total (rewrite appendAssociative args outer (ns ++ inner) in
                      (insertCaseNames {outer = args ++ outer} {inner} ns)
                  (rewrite sym (appendAssociative args outer inner) in 
                           sc)))
  insertCaseAltNames ns (ConstCase x sc) = ConstCase x (insertCaseNames ns sc)
  insertCaseAltNames ns (DefaultCase sc) = DefaultCase (insertCaseNames ns sc)

Weaken CaseTree where
  weakenNs ns t = insertCaseNames {outer = []} ns t 

mutual
  export
  embed : CaseTree args -> CaseTree (args ++ more)
  embed (Case x xs) = Case (elemExtend x) (map embedAlt xs)
  embed (STerm tm) = STerm (embed tm)
  embed (Unmatched msg) = Unmatched msg
  embed Impossible = Impossible

  embedAlt : CaseAlt args -> CaseAlt (args ++ more)
  embedAlt {args} {more} (ConCase n tag ns sc) 
       = ConCase n tag ns 
                 (rewrite (appendAssociative ns args more) in
                          (embed sc))
  embedAlt (ConstCase x sc) = ConstCase x (embed sc)
  embedAlt (DefaultCase sc) = DefaultCase (embed sc)

public export
data Pat = PCon Name Int (List Pat)
         | PConst Constant
         | PVar Name
         | PAny

Show Pat where
  show (PCon n i args) = show n ++ " " ++ show i ++ " " ++ assert_total (show args)
  show (PConst c) = show c
  show (PVar n) = show n
  show PAny = "_"

data NamedPats : List Name -> Type where
     Nil : NamedPats []
     (::) : Pat -> NamedPats ns -> NamedPats (n :: ns)

Show (NamedPats todo) where
  show xs = "[" ++ showAll xs ++ "]"
    where
      showAll : NamedPats ts -> String
      showAll [] = ""
      showAll [x] = show x
      showAll (x :: xs) = show x ++ ", " ++ showAll xs

(++) : NamedPats ms -> NamedPats ns -> NamedPats (ms ++ ns)
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

tail : NamedPats (p :: ps) -> NamedPats ps
tail (x :: xs) = xs

take : (as : List Name) -> NamedPats (as ++ bs) -> NamedPats as
take [] ps = []
take (x :: xs) (p :: ps) = p :: take xs ps

data PatClause : (todo : List Name) -> (done : List Name) -> Type where
     MkPatClause : NamedPats todo -> (rhs : Term done) -> PatClause todo done

Show (PatClause todo done) where
  show (MkPatClause ps rhs) = show ps ++ " => " ++ show rhs

data Partitions : List (PatClause todo done) -> Type where
     ConClauses : (cs : List (PatClause todo done)) ->
                  Partitions ps -> Partitions (cs ++ ps)
     VarClauses : (vs : List (PatClause todo done)) ->
                  Partitions ps -> Partitions (vs ++ ps)
     NoClauses : Partitions []

Show (Partitions ps) where
  show (ConClauses cs rest) = "CON " ++ show cs ++ ", " ++ show rest
  show (VarClauses vs rest) = "VAR " ++ show vs ++ ", " ++ show rest
  show NoClauses = "NONE"

thinClause : PatClause todo done -> PatClause todo (done ++ [a])
thinClause {a} {done} (MkPatClause ps rhs) 
    = MkPatClause ps (thin a {outer=done} {inner=[]} 
          (rewrite appendNilRightNeutral done in rhs))

dropNewArgs : (newargs : _) -> 
              PatClause (newargs ++ todo) done -> PatClause todo done
dropNewArgs [] pat = pat
dropNewArgs (x :: xs) (MkPatClause (y :: ys) rhs) 
    = dropNewArgs xs (MkPatClause ys rhs)

data ClauseType = ConClause | VarClause

clauseType : PatClause (a :: as) done -> ClauseType
clauseType (MkPatClause ((PCon x y xs) :: _) rhs) = ConClause
clauseType (MkPatClause ((PConst x) :: _) rhs) = ConClause
clauseType (MkPatClause ((PVar x) :: _) rhs) = VarClause
clauseType (MkPatClause (PAny :: _) rhs) = VarClause

partition : (ps : List (PatClause (a :: as) done)) -> Partitions ps
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

data Group : List Name -> List Name -> Type where
     ConGroup : Name -> (tag : Int) -> 
                List (PatClause (newargs ++ todo) done) ->
                Group todo (a :: done)
     ConstGroup : Constant -> List (PatClause todo done) ->
                  Group todo (a :: done)

data LengthMatch : List a -> List b -> Type where
     NilMatch : LengthMatch [] []
     ConsMatch : LengthMatch xs ys -> LengthMatch (x :: xs) (y :: ys)

checkLengthMatch : (xs : List a) -> (ys : List b) -> Maybe (LengthMatch xs ys)
checkLengthMatch [] [] = Just NilMatch
checkLengthMatch [] (x :: xs) = Nothing
checkLengthMatch (x :: xs) [] = Nothing
checkLengthMatch (x :: xs) (y :: ys) 
    = Just (ConsMatch !(checkLengthMatch xs ys))

data GroupMatch : ConType -> List Pat -> Group todo done -> Type where
  ConMatch : LengthMatch ps newargs ->
             GroupMatch (CName n tag) ps 
               (ConGroup {newargs} n tag (MkPatClause pats rhs :: rest))
  ConstMatch : GroupMatch (CConst c) []
                  (ConstGroup c (MkPatClause pats rhs :: rest))
  NoMatch : GroupMatch ct ps g

checkGroupMatch : (c : ConType) -> (ps : List Pat) -> (g : Group todo done) ->
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

nextNames : String -> List Pat -> State Int (args ** NamedPats args)
nextNames root [] = pure ([] ** [])
nextNames root (p :: pats) 
    = do (as ** ps) <- nextNames root pats
         n <- nextName root
         pure (n :: as ** p :: ps)

substPatNames : (ns : _) -> NamedPats ns -> Term vars -> Term vars
substPatNames [] [] tm = tm
substPatNames (n :: ns) (PVar pn :: ps) tm 
     = substName pn (Ref Bound n) (substPatNames ns ps tm)
substPatNames (n :: ns) (_ :: ps) tm = substPatNames ns ps tm

groupCons : List (PatClause (a :: todo) done) -> 
            State Int (List (Group todo (a :: done)))
groupCons cs = gc [] cs
  where
    addConG : Name -> (tag : Int) -> List Pat -> NamedPats todo ->
              (rhs : Term (a :: done)) ->
              (acc : List (Group todo (a :: done))) ->
              State Int (List (Group todo (a :: done)))
    -- Group all the clauses that begin with the same constructor, and
    -- add new pattern arguments for each of that constructor's arguments.
    -- The type of 'ConGroup' ensures that we refer to the arguments by
    -- the same name in each of the clauses
    addConG {a} {todo} n tag pargs pats rhs [] 
        = do (patnames ** newargs) <- nextNames "e" pargs
             pure [ConGroup n tag
               [MkPatClause {todo = patnames ++ todo} 
                  (newargs ++ pats) -- (refToLocals patnames 
                      (subst (Ref Bound a) (substPatNames patnames newargs rhs))]]
    addConG {a} {todo} n tag pargs pats rhs (g :: gs) with (checkGroupMatch (CName n tag) pargs g)
      addConG {a} {todo} n tag pargs pats rhs 
              ((ConGroup {newargs} n tag ((MkPatClause ps tm) :: rest)) :: gs)
                   | (ConMatch {newargs} y) 
        = let newclause = MkPatClause {todo = newargs ++ todo} 
                              (take newargs ps ++ pats) 
                              (subst (Ref Bound a) rhs) in 
              pure ((ConGroup n tag 
                    (newclause :: (MkPatClause ps tm) :: rest)) :: gs)
      addConG n tag pargs pats rhs (g :: gs) | NoMatch 
        = do gs' <- addConG n tag pargs pats rhs gs
             pure (g :: gs')
    
    addConstG : Constant -> NamedPats todo ->
                (rhs : Term (a :: done)) ->
                (acc : List (Group todo (a :: done))) ->
                State Int (List (Group todo (a :: done)))
    addConstG {a} c pats rhs [] 
        = pure [ConstGroup c [MkPatClause pats (subst (Ref Bound a) rhs)]]
    addConstG {a} c pats rhs (g :: gs) with (checkGroupMatch (CConst c) [] g)
      addConstG {a} c pats rhs 
              ((ConstGroup c ((MkPatClause ps tm) :: rest)) :: gs) | ConstMatch                    
          = let newclause = MkPatClause pats (subst (Ref Bound a) rhs) in
                pure ((ConstGroup c 
                      (newclause :: (MkPatClause ps tm) :: rest)) :: gs)
      addConstG c pats rhs (g :: gs) | NoMatch 
          = do gs' <- addConstG c pats rhs gs
               pure (g :: gs')

    addGroup : Pat -> NamedPats todo -> Term (a :: done) -> 
               List (Group todo (a :: done)) -> 
               State Int (List (Group todo (a :: done)))
    addGroup (PCon n t pargs) pats rhs acc 
        = addConG n t pargs pats rhs acc
    addGroup (PConst c) pats rhs acc 
        = addConstG c pats rhs acc
    addGroup _ pats rhs acc = pure acc -- Can't happen, not a constructor
        -- FIXME: Is this possible to rule out with a type? Probably.

    gc : List (Group todo (a :: done)) -> 
         List (PatClause (a :: todo) done) -> 
         State Int (List (Group todo (a :: done)))
    gc acc [] = pure acc
    gc {a} acc ((MkPatClause (pat :: pats) rhs) :: cs) 
        = do acc' <- addGroup pat pats (refToLocal a a rhs) acc
             gc acc' cs

localiseArgs : (newargs : _) -> 
               CaseTree (outer ++ vars) -> CaseTree (outer ++ newargs ++ vars)
localiseArgs {outer} {vars} newargs (Case var alts) 
    = Case (insertElemNames newargs var) (assert_total (map localise alts))
  where
    localise : CaseAlt (outer ++ vars) -> CaseAlt (outer ++ newargs ++ vars)
    localise (ConCase x tag args sc) 
      = ConCase x tag args 
          (rewrite appendAssociative args outer (newargs ++ vars) in
           (localiseArgs {outer = args ++ outer} {vars} newargs 
               (rewrite sym (appendAssociative args outer vars) in 
                  sc)))

    localise (ConstCase x sc) = ConstCase x (localiseArgs newargs sc)
    localise (DefaultCase sc) = DefaultCase (localiseArgs newargs sc)
localiseArgs {outer} newargs (STerm tm) 
    = STerm (innerRefToLocals {outer} newargs tm)
localiseArgs newargs (Unmatched msg) = Unmatched msg
localiseArgs newargs Impossible = Impossible

mutual
  {- 'PatClause' contains a list of patterns still to process (that's the 
     "todo") and a right hand side for the patterns already processed (that's 
     the "done"). So "match" builds the remainder of the case tree for
     the unprocessed patterns. "err" is the tree for when the patterns don't
     cover the input (i.e. the "fallthrough" pattern, which at the top
     level will be an error). -}
  match : List (PatClause todo done) -> (err : CaseTree (done ++ todo)) -> 
               State Int (CaseTree (done ++ todo))
  match {todo = []} [] err = pure err
  match {todo = []} {done} ((MkPatClause [] rhs) :: _) err 
       = pure $ STerm (rewrite appendNilRightNeutral done in rhs)
  match {todo = (_ :: _)} clauses err 
      = let ps = partition clauses in
            mixture (partition clauses) err

  caseGroups : List (Group todo (a :: done)) -> CaseTree (done ++ a :: todo) ->
               State Int (CaseTree (done ++ a :: todo))
  caseGroups {a} {todo} {done} gs errorCase
      = do g <- altGroups gs
           pure (Case {var = a} localPrf g)
    where
      altGroups : List (Group todo (a :: done)) -> 
                  State Int (List (CaseAlt (done ++ a :: todo)))
      altGroups [] = pure [DefaultCase errorCase]
      altGroups (ConGroup {newargs} cn tag rest :: cs) 
          = do -- do the remaining patterns, without newargs 
               crest <- assert_total $ match {todo} {done = done ++ [a]} 
                             (map (\x => dropNewArgs newargs (thinClause x)) rest)
                             (rewrite sym (appendAssociative done [a] todo) in 
                                      errorCase) 
               cs' <- altGroups cs
               pure (ConCase cn tag newargs 
                      (localiseArgs {outer = []} {vars = done ++ a :: todo} 
                                    newargs 
                       (rewrite (appendAssociative done [a] todo) in crest)) 
                         :: cs')
      altGroups (ConstGroup c rest :: cs) 
          = do crest <- assert_total $ match {todo} {done = done ++ [a]} 
                             (map thinClause rest)
                             (rewrite sym (appendAssociative done [a] todo) in 
                                      errorCase) 
               cs' <- altGroups cs
               pure (ConstCase c 
                      (rewrite appendAssociative done [a] todo in
                          crest) :: cs')

  conRule : List (PatClause (a :: todo) done) -> CaseTree (done ++ a :: todo) -> 
            State Int (CaseTree (done ++ a :: todo))
  conRule cs err 
      = do groups <- groupCons cs
           caseGroups groups err

  varRule : List (PatClause (a :: todo) done) -> CaseTree (done ++ a :: todo) -> 
            State Int (CaseTree (done ++ a :: todo))
  varRule {a} {done} {todo} alts err
      = do let alts' = map (repVar a) alts
           rest <- match {done = done ++ [a]} alts' 
                      (rewrite sym (appendAssociative done [a] todo) in 
                               err)
           (rewrite appendAssociative done [a] todo in pure rest)
    where
      -- Turn the pattern name into a locally bound nameless variable on
      -- the RHS. Use the variable name if given, or nothing if not
      repVar : (a : Name) -> PatClause (a :: todo) done -> PatClause todo (done ++ [a])
      repVar a (MkPatClause (PVar n :: pats) rhs) 
        = MkPatClause pats (mkLocal n {new=a} {later=done} {vars=[]} 
                                           localPrf
              (rewrite appendNilRightNeutral done in rhs))
      repVar a (MkPatClause (p :: pats) rhs) 
        = MkPatClause pats (mkLocal a {new=a} {later=done} {vars=[]} 
                                           localPrf
              (rewrite appendNilRightNeutral done in rhs))

  mixture : {ps : List (PatClause (a :: todo) done)} ->
            Partitions ps -> CaseTree (done ++ a :: todo) -> 
            State Int (CaseTree (done ++ a :: todo))
  mixture (ConClauses cs rest) err 
      = do fallthrough <- mixture rest err
           conRule cs fallthrough
  mixture (VarClauses vs rest) err 
      = do fallthrough <- mixture rest err
           varRule vs fallthrough
  mixture NoClauses err = pure err

public export
data CaseError = DifferingArgNumbers

mkPatClause : (args : List Name) -> (List Pat, ClosedTerm) ->
              Either CaseError (PatClause args [])
mkPatClause args (ps, rhs) 
    = case checkLengthMatch args ps of
           Nothing => Left DifferingArgNumbers
           Just eq => Right (MkPatClause (mkNames args ps eq) rhs)
  where
    mkNames : (args : List Name) -> (ps : List Pat) -> 
              LengthMatch args ps -> NamedPats args
    mkNames [] [] NilMatch = []
    mkNames (arg :: args) (p :: ps) (ConsMatch eq)
        = p :: mkNames args ps eq

export
patCompile : List (List Pat, ClosedTerm) -> CaseTree [] ->
             Either CaseError (args ** CaseTree args)
patCompile [] def = pure ([] ** def)
patCompile (p :: ps) def 
    = do let ns = getNames 0 (fst p)
         pats <- traverse (mkPatClause ns) (p :: ps)
         let cases = evalState (match pats 
                                (rewrite sym (appendNilRightNeutral ns) in
                                         (weakenNs ns def))) 0
         pure (ns ** cases)
  where
    getNames : Int -> List Pat -> List Name
    getNames i [] = []
    getNames i (x :: xs) = MN "arg" i :: getNames (i + 1) xs

-- A test case

plusClauses : List (PatClause [UN "x", UN "y"] [])
plusClauses =
   [MkPatClause [PCon (UN "S") 1 [PVar (UN "k")], PCon (UN "S") 1 [PVar (UN "y")]]
                     (Ref Bound (UN "k")),
    MkPatClause [PCon (UN "Z") 0 [], PVar (UN "y")] 
                     (Ref Bound (UN "y"))]

export
testPlus : Name -> CaseTree [UN "x", UN "y"]
testPlus plus
    = Case Here
          [ConCase (UN "Z") 0 []
            (STerm (Local {x = UN "y"} (There Here))),
           ConCase (UN "S") 1 [UN "k"]
            (STerm (App (Ref (DataCon 1 1) (UN "S")) 
            (App (App (Ref Func plus) 
                  (Local {x = UN "k"} Here)) 
                  (Local {x = UN "y"} (There (There Here))))))
          ]
