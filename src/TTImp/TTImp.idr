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
     IApp : annot -> 
            (fn : RawImp annot) -> (arg : RawImp annot) -> RawImp annot
     IPrimVal : annot -> Constant -> RawImp annot
     IType : annot -> RawImp annot
     IBindVar : annot -> String -> RawImp annot -- a name to be implicitly bound
     Implicit : annot -> RawImp annot
-- TODO: IDotted (things which must be solved by inference and checked
-- against what's given)

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
  show (IApp _ fn arg) 
      = "(" ++ show fn ++ " " ++ show arg ++ ")"
  show (IPrimVal _ y) = show y
  show (IType _) = "Type"
  show (IBindVar _ n) = "$" ++ show n
  show (Implicit _) = "_"

export
getAnnot : RawImp a -> a
getAnnot (IVar x _) = x
getAnnot (IPi x _ _ _ _) = x
getAnnot (ILam x _ _ _ _) = x
getAnnot (ILet x _ _ _ _) = x
getAnnot (IApp x _ _) = x
getAnnot (IPrimVal x _) = x
getAnnot (IType x) = x
getAnnot (IBindVar x _) = x
getAnnot (Implicit x) = x

export
apply : RawImp a -> List (RawImp a) -> RawImp a
apply f [] = f
apply f (x :: xs) = apply (IApp (getAnnot f) f x) xs

-- Top level declarations: types, clauses and data

public export
data ImpTy : Type -> Type where
     MkImpTy : annot -> (n : Name) -> (ty : RawImp annot) -> ImpTy annot

export
Show (ImpTy annot) where
  show (MkImpTy _ n ty) = show n ++ " : " ++ show ty

public export
data ImpClause : Type -> Type where
     MkImpClause : annot -> (lhs : RawImp annot) -> (rhs : RawImp annot) ->
                   ImpClause annot

export
Show (ImpClause annot) where
  show (MkImpClause _ lhs rhs) = show lhs ++ " = " ++ show rhs

public export
data ImpData : Type -> Type where
     MkImpData : annot -> (n : Name) -> (tycon : RawImp annot) ->
                 (datacons : List (ImpTy annot)) -> ImpData annot

export
Show (ImpData annot) where
  show (MkImpData _ n tycon dcons)
      = "data " ++ show n ++ " : " ++ show tycon ++ " where {\n\t" ++
        showSep "\n\t" (map show dcons) ++ "\n}"

public export
data ImpDecl : Type -> Type where
     IClaim : annot -> ImpTy annot -> ImpDecl annot
     IDef : annot -> Name -> List (ImpClause annot) -> ImpDecl annot
     IData : annot -> ImpData annot -> ImpDecl annot
     ImplicitNames : annot -> List (String, RawImp annot) -> ImpDecl annot

export
Show (ImpDecl annot) where
  show (IClaim _ ty) = show ty
  show (IDef _ n cs) = show n ++ " clauses:\n\t" ++ 
                       showSep "\n\t" (map show cs)
  show (IData _ d) = show d
  show (ImplicitNames _ ns) = "implicit " ++ show ns

-- State which is useful to preserve throughout elaborating a file
public export
record ImpState annot where
  constructor MkImpState
  impNames : List (String, RawImp annot) -- names which can be implicitly bound

initImpState : ImpState annot
initImpState = MkImpState []

-- A label for TTImp state in the global state
export
data ImpST : Type where

export
setupImpState : CoreM annot [] [ImpST ::: ImpState annot] ()
setupImpState = new ImpST initImpState

export
deleteImpState : CoreM annot [ImpST ::: ImpState annot] [] ()
deleteImpState = delete ImpST

export
addImp : String -> RawImp annot -> Core annot [ImpST ::: ImpState annot] ()
addImp str ty
    = do ist <- get ImpST
         put ImpST (record { impNames $= ((str, ty) ::) } ist)

