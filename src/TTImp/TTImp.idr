module TTImp.TTImp

import Core.TT
import Core.Context
import Core.UnifyState

import Data.List
import Data.CSet

%default covering

-- Unchecked terms, with implicit arguments
-- This is the raw, elaboratable form.
-- Higher level expressions (e.g. case, pattern matching let, where blocks,
-- do notation, etc, should elaborate via this, perhaps in some local 
-- context).

-- Parameterised by an annotation type, which allows higher level expressions
-- to record the provenance of RawImp expressions (e.g. source file, location,
-- original expression, etc)
mutual
  public export
  data RawImp : (annotation : Type) -> Type where
       IVar : annot -> Name -> RawImp annot
       IPi : annot -> RigCount -> PiInfo -> Maybe Name -> 
             (argTy : RawImp annot) -> (retTy : RawImp annot) -> RawImp annot
       ILam : annot -> RigCount -> PiInfo -> Name -> 
              (argTy : RawImp annot) -> (scope : RawImp annot) -> RawImp annot
       ILet : annot -> RigCount -> Name -> 
              (nTy : RawImp annot) -> (nVal : RawImp annot) -> 
              (scope : RawImp annot) ->
              RawImp annot
       ICase : annot -> RawImp annot -> List (ImpClause annot) -> RawImp annot
       ILocal : annot -> List (ImpDecl annot) -> RawImp annot -> RawImp annot
       IApp : annot -> 
              (fn : RawImp annot) -> (arg : RawImp annot) -> RawImp annot
       IImplicitApp : annot -> 
              (fn : RawImp annot) -> Name -> (arg : RawImp annot) -> RawImp annot
       ISearch : annot -> (depth : Nat) -> RawImp annot
       IAlternative : annot -> (unique : Bool) -> 
                      List (RawImp annot) -> RawImp annot
       ICoerced : annot -> RawImp annot -> RawImp annot
       IPrimVal : annot -> Constant -> RawImp annot
       IHole : annot -> String -> RawImp annot
       IType : annot -> RawImp annot
       IBindVar : annot -> String -> RawImp annot -- a name to be implicitly bound
       IAs : annot -> String -> (pattern : RawImp annot) -> RawImp annot
       IMustUnify : annot -> (pattern : RawImp annot) -> RawImp annot
       Implicit : annot -> RawImp annot

  -- Top level declarations: types, clauses and data
  public export
  data ImpTy : Type -> Type where
       MkImpTy : annot -> (n : Name) -> (ty : RawImp annot) -> ImpTy annot

  public export
  data ImpClause : Type -> Type where
       PatClause : annot -> (lhs : RawImp annot) -> (rhs : RawImp annot) ->
                   ImpClause annot
       ImpossibleClause : annot -> (lhs : RawImp annot) -> ImpClause annot
       -- TODO: WithClause
  
  public export
  data DataOpt : Type where
       SearchBy : List Name -> DataOpt -- determining arguments
       NoHints : DataOpt -- Don't generate search hints for constructors

  export
  Eq DataOpt where
    (==) (SearchBy xs) (SearchBy ys) = xs == ys
    (==) NoHints NoHints = True
    (==) _ _ = False

  public export
  data ImpData : Type -> Type where
       MkImpData : annot -> (n : Name) -> (tycon : RawImp annot) ->
                   (opts : List DataOpt) ->
                   (datacons : List (ImpTy annot)) -> ImpData annot
  
  public export
  data FnOpt : Type where
       Inline : FnOpt
       Hint : FnOpt
       GlobalHint : FnOpt

  public export
  data ImpDecl : Type -> Type where
       IClaim : annot -> Visibility -> List FnOpt -> ImpTy annot -> ImpDecl annot
       IDef : annot -> Name -> List (ImpClause annot) -> ImpDecl annot
       IData : annot -> Visibility -> ImpData annot -> ImpDecl annot
       INamespace : annot -> List String -> List (ImpDecl annot) ->
                    ImpDecl annot
       IReflect : annot -> RawImp annot -> ImpDecl annot
       ImplicitNames : annot -> List (String, RawImp annot) -> ImpDecl annot
       IHint : annot -> (hintname : Name) -> (target : Maybe Name) -> 
               ImpDecl annot
       IPragma : (Ref Ctxt Defs -> Core annot ()) -> ImpDecl annot
       ILog : Nat -> ImpDecl annot
       -- To add: IRecord

mutual
  -- assume RHS (so no IBindVar or anything pattern match related)
  -- Intention is to find unused names in a case block so that we can
  -- give them the right multiplicity in the generated type, if any names
  -- are used linearly
  used : SortedSet -> RawImp annot -> SortedSet
  used ns (IVar x n) 
     = if contains n ns then empty else insert n empty
  used ns (IPi _ _ _ bn argTy retTy) 
     = let ns' = maybe ns (\n => insert n ns) bn in
           union (used ns' argTy) (used ns' retTy)
  used ns (ILam _ _ _ n argTy scope) 
     = union (used ns argTy) (used ns scope)
  used ns (ILet _ _ n nTy nVal scope) 
     = union (union (used ns nTy) (used ns nVal)) (used ns scope)
  used ns (ICase _ sc xs) 
     = union (used ns sc) (usedCases ns xs)
  used ns (ILocal _ ds sc) 
     = union (usedDecls ns ds) (used ns sc)
  used ns (IApp _ fn arg) 
     = union (used ns fn) (used ns arg)
  used ns (IImplicitApp _ fn _ arg)
     = union (used ns fn) (used ns arg)
  used ns (IAlternative _ _ alts)
     = foldr (\alt => union (used ns alt)) empty alts
  used ns _ = empty

  bindVars : RawImp annot -> SortedSet
  bindVars (IBindVar _ n) = insert (UN n) empty
  bindVars (IApp _ f a) = union (bindVars f) (bindVars a)
  bindVars (IImplicitApp _ f _ a) = union (bindVars f) (bindVars a)
  bindVars (IAs _ n p) = insert (UN n) (bindVars p)
  bindVars _ = empty

  usedCases : SortedSet -> List (ImpClause annot) -> SortedSet
  usedCases ns [] = empty
  usedCases ns (ImpossibleClause _ _ :: rest) = usedCases ns rest
  usedCases ns (PatClause _ lhs rhs :: rest)
      = union (used (union (bindVars lhs) ns) rhs)
              (usedCases ns rest)

  usedDecls : SortedSet -> List (ImpDecl annot) -> SortedSet
  usedDecls ns [] = empty
  usedDecls ns (IDef _ n cs :: rest) 
      = union (usedCases ns cs) (usedDecls ns rest)
  usedDecls ns (_ :: rest) = usedDecls ns rest


-- Return all the names which are used but not bound in the term
export
usedNames : RawImp annot -> List Name
usedNames = toList . used empty

export
usedInAlts : List (ImpClause annot) -> List Name
usedInAlts = toList . usedCases empty

-- REPL commands for TTImp interaction
public export
data ImpREPL : Type -> Type where
     Eval : RawImp annot -> ImpREPL annot
     Check : RawImp annot -> ImpREPL annot
     ProofSearch : Name -> ImpREPL annot
     DebugInfo : Name -> ImpREPL annot
     Quit : ImpREPL annot

-- Information about names in nested blocks
public export
record NestedNames (vars : List Name) where
  constructor MkNested
  -- A map from names to the decorated version of the name, and the new name
  -- applied to its enclosing environment
  names : List (Name, (Name, Term vars))

export
Weaken NestedNames where
  weaken (MkNested ns) = MkNested (map wknName ns)
    where
      wknName : (Name, (Name, Term vars)) ->
                (Name, (Name, Term (n :: vars)))
      wknName (n, (n', rep)) = (n, (n', weaken rep))

export
dropName : Name -> NestedNames vars -> NestedNames vars
dropName n nest = record { names $= drop } nest
  where
    drop : List (Name, a) -> List (Name, a)
    drop [] = []
    drop ((x, y) :: xs) 
        = if x == n then drop xs 
             else (x, y) :: drop xs

export
definedInBlock : List (ImpDecl annot) -> List Name
definedInBlock = concatMap defName
  where
    getName : ImpTy annot -> Name
    getName (MkImpTy _ n _) = n

    defName : ImpDecl annot -> List Name
    defName (IClaim _ _ _ ty) = [getName ty]
    defName (IData _ _ (MkImpData _ n _ _ cons)) = n :: map getName cons
    defName _ = []

export
getAnnot : RawImp a -> a
getAnnot (IVar x _) = x
getAnnot (IPi x _ _ _ _ _) = x
getAnnot (ILam x _ _ _ _ _) = x
getAnnot (ILet x _ _ _ _ _) = x
getAnnot (ICase x _ _) = x
getAnnot (ILocal x _ _) = x
getAnnot (IApp x _ _) = x
getAnnot (IImplicitApp x _ _ _) = x
getAnnot (ISearch x _) = x
getAnnot (IAlternative x _ _) = x
getAnnot (ICoerced x _) = x
getAnnot (IPrimVal x _) = x
getAnnot (IHole x _) = x
getAnnot (IType x) = x
getAnnot (IBindVar x _) = x
getAnnot (IMustUnify x _) = x
getAnnot (IAs x _ _) = x
getAnnot (Implicit x) = x

export
apply : RawImp a -> List (RawImp a) -> RawImp a
apply f [] = f
apply f (x :: xs) = apply (IApp (getAnnot f) f x) xs

export
getFn : RawImp a -> RawImp a
getFn (IApp _ f arg) = getFn f
getFn (IImplicitApp _ f _ _) = getFn f
getFn f = f

export
explicitLazy : Defs -> RawImp annot -> Bool
explicitLazy defs (IVar _ n)
   = isDelay n defs || isForce n defs
explicitLazy defs _ = False
 
mutual
  export
  Show (RawImp annot) where
    show (IVar _ nm) = show nm
    show (IPi _ _ Implicit n argTy retTy) 
        = "(%imppi (" ++ show n ++ " " ++ show argTy ++ ") " 
               ++ show retTy ++ ")"
    show (IPi _ _ _ n argTy retTy)
        = "(%pi (" ++ show n ++ " " ++ show argTy ++ ") " 
               ++ show retTy ++ ")"
    show (ILam _ _ _ n argTy scope) 
        = "(%lam (" ++ show n ++ " " ++ show argTy ++ ") " 
               ++ show scope ++ ")"
    show (ILet _ _ n nTy nVal scope)
        = "(%let (" ++ show n ++ " " ++ show nTy ++ " " ++ show nVal ++ ") "
               ++ show scope ++ ")"
    show (ICase _ scr alts)
        = "(%case (" ++ show scr ++ ") " ++ show alts ++ ")"
    show (ILocal _ def scope)
        = "(%local (" ++ show def ++ ") " ++ show scope ++ ")"
    show (IApp _ fn arg) 
        = "(" ++ show fn ++ " " ++ show arg ++ ")"
    show (IImplicitApp _ fn n arg) 
        = show fn ++ " {" ++ show n ++ " = " ++ show arg ++ "}"
    show (ISearch _ n) 
        = "%search"
    show (IAlternative _ u alts) 
        = "(|" ++ showSep "," (map show alts) ++ "|)"
    show (ICoerced _ tm) = show tm
    show (IPrimVal _ y) = show y
    show (IHole _ x) = "?" ++ x
    show (IType _) = "Type"
    show (IBindVar _ n) = "$" ++ show n
    show (IMustUnify _ tm) = "(." ++ show tm ++ ")"
    show (IAs _ n tm) = n ++ "@(" ++ show tm ++ ")"
    show (Implicit _) = "_"

  export
  Show (ImpTy annot) where
    show (MkImpTy _ n ty) = show n ++ " : " ++ show ty

  export
  Show (ImpClause annot) where
    show (PatClause _ lhs rhs) = show lhs ++ " = " ++ show rhs
    show (ImpossibleClause _ lhs) = show lhs ++ " impossible"

  export
  Show (ImpData annot) where
    show (MkImpData _ n tycon dopts dcons)
        = "data " ++ show n ++ " : " ++ show tycon ++ " where {\n\t" ++
          showSep "\n\t" (map show dcons) ++ "\n}"

  export
  Show (ImpDecl annot) where
    show (IClaim _ _ _ ty) = show ty
    show (IDef _ n cs) = show n ++ " clauses:\n\t" ++ 
                         showSep "\n\t" (map show cs)
    show (IData _ _ d) = show d
    show (INamespace _ ns decls) 
        = "namespace " ++ show ns ++ 
          showSep "\n" (assert_total $ map show decls)
    show (IReflect _ tm)
        = "%runElab " ++ show tm
    show (ImplicitNames _ ns) = "implicit " ++ show ns
    show (IHint _ n t) = "%hint " ++ show n ++ " " ++ show t
    show (IPragma _) = "[externally defined pragma]"
    show (ILog lvl) = "%logging " ++ show lvl

-- State which is useful to preserve throughout elaborating a file
public export
record ImpState annot where
  constructor MkImpState
  impNames : List (String, RawImp annot) -- names which can be implicitly bound

export
initImpState : ImpState annot
initImpState = MkImpState []

-- A label for TTImp state in the global state
export
data ImpST : Type where

export
addImp : {auto i : Ref ImpST (ImpState annot)} ->
         String -> RawImp annot -> Core annot ()
addImp str ty
    = do ist <- get ImpST
         put ImpST (record { impNames $= ((str, ty) ::) } ist)

-- Update the lhs of a clause so that the name is fully explicit, and
-- by default is in the current namespace
export
lhsInCurrentNS : {auto c : Ref Ctxt Defs} ->
                 NestedNames vars -> RawImp annot -> Core annot (RawImp annot)
lhsInCurrentNS nest (IApp loc f a)
    = do f' <- lhsInCurrentNS nest f
         pure (IApp loc f' a)
lhsInCurrentNS nest (IVar loc n)
    = case lookup n (names nest) of
           Nothing =>
              do n' <- inCurrentNS n
                 pure (IVar loc n')
           -- If it's one of the names in the current nested block, we'll
           -- be rewriting it during elaboration to be in the scope of the
           -- parent name.
           Just _ => pure (IVar loc n)
lhsInCurrentNS nest tm = pure tm
         

remove : Maybe Name -> List (String, a) -> List (String, a)
remove (Just (UN n)) xs = removeN n xs
  where
    removeN : String -> List (String, a) -> List (String, a)
    removeN str [] = []
    removeN str ((n, ty) :: ns) 
        = if str == n 
             then ns
             else (n, ty) :: removeN str ns
remove _ xs = xs

addBindImps : List (String, RawImp annot) -> 
              (used : List (String, RawImp annot)) ->
              RawImp annot -> (RawImp annot, List (String, RawImp annot))
addBindImps is used (IVar x (UN n)) 
    = case lookup n is of
           Nothing => (IVar x (UN n), used)
           Just (Implicit _) => (IBindVar x n, used)
           -- if it's in 'used' with a type, use that again, otherwise
           -- bind names in the type and add to 'used'
           Just ty => maybe
                         (let (ty', used1) = addBindImps is used ty in
                              (IVar x (UN n), (n, ty') :: used))
                         (\_ => (IVar x (UN n), used))
                         (lookup n used)
addBindImps is used (IVar x n) = (IVar x n, used)
addBindImps is used (IPi x c y n argTy retTy) 
    = let (arg', used1) = addBindImps is used argTy
          (ret', used2) = addBindImps (remove n is) used1 retTy in
          (IPi x c y n arg' ret', used2)
addBindImps is used (ILam x c y n argTy scope) 
    = let (arg', used1) = addBindImps is used argTy
          (scope', used2) = addBindImps (remove (Just n) is) used1 scope in
          (ILam x c y n arg' scope', used2)
addBindImps is used (ILet x c n nTy nVal scope) 
    = let (ty', used1) = addBindImps is used nTy
          (val', used2) = addBindImps is used1 nVal 
          (scope', used3) = addBindImps (remove (Just n) is) used2 scope in
          (ILet x c n ty' val' scope', used3)
addBindImps is used (IApp x fn arg) 
    = let (fn', used1) = addBindImps is used fn
          (arg', used2) = addBindImps is used1 arg in
          (IApp x fn' arg', used2)
addBindImps is used (IImplicitApp x fn n arg) 
    = let (fn', used1) = addBindImps is used fn
          (arg', used2) = addBindImps is used1 arg in
          (IImplicitApp x fn' n arg', used2)
addBindImps is used tm = (tm, used)

bindWith : annot ->
           List (String, RawImp annot) -> List (String, RawImp annot) ->
           RawImp annot -> RawImp annot
bindWith loc is [] tm = tm
bindWith loc [] used tm = tm
bindWith loc ((n, _) :: ns) used tm
    = case lookup n used of
           Nothing => bindWith loc ns used tm
           Just ty => bindWith loc ns used 
                         (IPi loc RigW Implicit (Just (UN n)) ty tm)

-- convert any 'impName' without a type to an IBindVar, so that it gets
-- bound when it's first used.
-- Any name which occurs in impNames *with* a type gets an IPi Implicit binder
-- at the front
-- Any name in the current environment won't be bound
export
mkBindImps : {auto i : Ref ImpST (ImpState annot)} ->
             Env Term vars ->
             RawImp annot -> 
             Core annot (RawImp annot)
mkBindImps env tm 
    = do ist <- get ImpST
         let (btm, ns) = addBindImps (removeNames env (impNames ist)) [] tm
         pure (bindWith (getAnnot tm) (removeNames env (impNames ist)) ns btm)
  where
    removeNames : Env Term vars -> List (String, a) -> List (String, a)
    removeNames [] is = is
    removeNames ((::) {x} b bs) is = removeNames bs (remove (Just x) is)

-- Turn names into pattern variables as IBindVar
-- This considers a name a pattern variable if it begins with a lower case
-- letter, and isn't applied to any arguments
export
mkLCPatVars : RawImp annot -> RawImp annot
mkLCPatVars tm = mkPatVars True tm
  where
    implicitName : List Char -> Bool
    implicitName (c :: cs) = isLower c
    implicitName _ = False

    mkPatVars : (notfn : Bool) -> RawImp annot -> RawImp annot
    mkPatVars False (IVar loc (UN n))
        = if implicitName (unpack n) 
             then IBindVar loc n
             else IVar loc (UN n)
    mkPatVars notfn (IApp loc f arg) 
        = IApp loc (mkPatVars True f) (mkPatVars False arg)
    mkPatVars notfn (IImplicitApp loc f n arg) 
        = IImplicitApp loc (mkPatVars True f) n (mkPatVars False arg)
    mkPatVars notfn (IMustUnify loc tm) 
        = IMustUnify loc (mkPatVars notfn tm)
    mkPatVars notfn (IAs loc n tm) 
        = IAs loc n (mkPatVars notfn tm)
    mkPatVars notfn tm = tm
