module TTImp.TTImp

import Core.TT
import Core.Context
import Core.UnifyState

import Data.List

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
       IPi : annot -> PiInfo -> Maybe Name -> 
             (argTy : RawImp annot) -> (retTy : RawImp annot) -> RawImp annot
       ILam : annot -> PiInfo -> Name -> 
              (argTy : RawImp annot) -> (scope : RawImp annot) -> RawImp annot
       ILet : annot -> Name -> 
              (nTy : RawImp annot) -> (nVal : RawImp annot) -> 
              (scope : RawImp annot) ->
              RawImp annot
       ILocal : annot -> List (ImpDecl annot) -> RawImp annot -> RawImp annot
       IApp : annot -> 
              (fn : RawImp annot) -> (arg : RawImp annot) -> RawImp annot
       IImplicitApp : annot -> 
              (fn : RawImp annot) -> Name -> (arg : RawImp annot) -> RawImp annot
       ISearch : annot -> (depth : Nat) -> RawImp annot
       IAlternative : annot -> (unique : Bool) -> 
                      List (RawImp annot) -> RawImp annot
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
       MkImpClause : annot -> (lhs : RawImp annot) -> (rhs : RawImp annot) ->
                     ImpClause annot

  public export
  data ImpData : Type -> Type where
       MkImpData : annot -> (n : Name) -> (tycon : RawImp annot) ->
                   (datacons : List (ImpTy annot)) -> ImpData annot

  public export
  data ImpDecl : Type -> Type where
       IClaim : annot -> ImpTy annot -> ImpDecl annot
       IDef : annot -> Name -> List (ImpClause annot) -> ImpDecl annot
       IData : annot -> ImpData annot -> ImpDecl annot
       INamespace : annot -> List String -> ImpDecl annot
       ImplicitNames : annot -> List (String, RawImp annot) -> ImpDecl annot
       ILog : Nat -> ImpDecl annot

-- REPL commands for TTImp interaction
public export
data ImpREPL : Type -> Type where
     Eval : RawImp annot -> ImpREPL annot
     Check : RawImp annot -> ImpREPL annot
     ProofSearch : Name -> ImpREPL annot
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
    defName (IClaim _ ty) = [getName ty]
    defName (IData _ (MkImpData _ n _ cons)) = n :: map getName cons
    defName _ = []

export
getAnnot : RawImp a -> a
getAnnot (IVar x _) = x
getAnnot (IPi x _ _ _ _) = x
getAnnot (ILam x _ _ _ _) = x
getAnnot (ILet x _ _ _ _) = x
getAnnot (ILocal x _ _) = x
getAnnot (IApp x _ _) = x
getAnnot (IImplicitApp x _ _ _) = x
getAnnot (ISearch x _) = x
getAnnot (IAlternative x _ _) = x
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

mutual
  export
  Show (RawImp annot) where
    show (IVar _ nm) = show nm
    show (IPi _ Implicit n argTy retTy) 
        = "(%imppi (" ++ show n ++ " " ++ show argTy ++ ") " 
               ++ show retTy ++ ")"
    show (IPi _ _ n argTy retTy)
        = "(%pi (" ++ show n ++ " " ++ show argTy ++ ") " 
               ++ show retTy ++ ")"
    show (ILam _ _ n argTy scope) 
        = "(%lam (" ++ show n ++ " " ++ show argTy ++ ") " 
               ++ show scope ++ ")"
    show (ILet _ n nTy nVal scope)
        = "(%let (" ++ show n ++ " " ++ show nTy ++ " " ++ show nVal ++ ") "
               ++ show scope ++ ")"
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
    show (MkImpClause _ lhs rhs) = show lhs ++ " = " ++ show rhs

  export
  Show (ImpData annot) where
    show (MkImpData _ n tycon dcons)
        = "data " ++ show n ++ " : " ++ show tycon ++ " where {\n\t" ++
          showSep "\n\t" (map show dcons) ++ "\n}"

  export
  Show (ImpDecl annot) where
    show (IClaim _ ty) = show ty
    show (IDef _ n cs) = show n ++ " clauses:\n\t" ++ 
                         showSep "\n\t" (map show cs)
    show (IData _ d) = show d
    show (INamespace _ ns) = "namespace " ++ show ns
    show (ImplicitNames _ ns) = "implicit " ++ show ns
    show (ILog lvl) = "logging " ++ show lvl

-- State which is useful to preserve throughout elaborating a file
public export
record ImpState annot where
  constructor MkImpState
  impNames : List (String, RawImp annot) -- names which can be implicitly bound
  currentNS : List String -- Current namespace, default "Main"

export
initImpState : ImpState annot
initImpState = MkImpState [] ["Main"]

-- A label for TTImp state in the global state
export
data ImpST : Type where

export
addImp : {auto i : Ref ImpST (ImpState annot)} ->
         String -> RawImp annot -> Core annot ()
addImp str ty
    = do ist <- get ImpST
         put ImpST (record { impNames $= ((str, ty) ::) } ist)

-- Set the default namespace for new definitions
export
setNS : {auto i : Ref ImpST (ImpState annot)} ->
        List String -> Core annot ()
setNS ns
    = do ist <- get ImpST
         put ImpST (record { currentNS = ns } ist)

-- Add a new nested namespace to the current namespace for new definitions
-- e.g. extendNS ["Data"] when namespace is "Prelude.List" leads to
-- current namespace of "Prelude.List.Data"
-- Inner namespaces go first, for ease of name lookup
export
extendNS : {auto i : Ref ImpST (ImpState annot)} ->
           List String -> Core annot ()
extendNS ns
    = do ist <- get ImpST
         put ImpST (record { currentNS $= (++ (reverse ns)) } ist)

-- Get the name as it would be defined in the current namespace
-- i.e. if it doesn't have an explicit namespace already, add it,
-- otherwise leave it alone
export
inCurrentNS : {auto i : Ref ImpST (ImpState annot)} ->
              Name -> Core annot Name
inCurrentNS (UN n)
    = do ist <- get ImpST
         pure (NS (currentNS ist) (UN n))
inCurrentNS n = pure n

-- Update the lhs of a clause so that the name is fully explicit, and
-- by default is in the current namespace
export
lhsInCurrentNS : {auto i : Ref ImpST (ImpState annot)} ->
                 RawImp annot -> Core annot (RawImp annot)
lhsInCurrentNS (IApp loc f a)
    = do f' <- lhsInCurrentNS f
         pure (IApp loc f' a)
lhsInCurrentNS (IVar loc n)
    = do n' <- inCurrentNS n
         pure (IVar loc n')
lhsInCurrentNS tm = pure tm
         

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
addBindImps is used (IPi x y n argTy retTy) 
    = let (arg', used1) = addBindImps is used argTy
          (ret', used2) = addBindImps (remove n is) used1 retTy in
          (IPi x y n arg' ret', used2)
addBindImps is used (ILam x y n argTy scope) 
    = let (arg', used1) = addBindImps is used argTy
          (scope', used2) = addBindImps (remove (Just n) is) used1 scope in
          (ILam x y n arg' scope', used2)
addBindImps is used (ILet x n nTy nVal scope) 
    = let (ty', used1) = addBindImps is used nTy
          (val', used2) = addBindImps is used1 nVal 
          (scope', used3) = addBindImps (remove (Just n) is) used2 scope in
          (ILet x n ty' val' scope', used3)
addBindImps is used (IApp x fn arg) 
    = let (fn', used1) = addBindImps is used fn
          (arg', used2) = addBindImps is used1 arg in
          (IApp x fn' arg', used2)
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
                         (IPi loc Implicit (Just (UN n)) ty tm)

-- convert any 'impName' without a type to an IBindVar, so that it gets
-- bound when it's first used.
-- Any name which occurs in impNames *with* a type gets an IPi Implicit binder
-- at the front
export
mkBindImps : {auto i : Ref ImpST (ImpState annot)} ->
             RawImp annot -> 
             Core annot (RawImp annot)
mkBindImps tm 
    = do ist <- get ImpST
         let (btm, ns) = addBindImps (impNames ist) [] tm
         pure (bindWith (getAnnot tm) (impNames ist) ns btm)

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
    mkPatVars notfn (IMustUnify loc tm) 
        = IMustUnify loc (mkPatVars notfn tm)
    mkPatVars notfn (IAs loc n tm) 
        = IAs loc n (mkPatVars notfn tm)
    mkPatVars notfn tm = tm
