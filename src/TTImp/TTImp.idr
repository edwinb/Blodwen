module TTImp.TTImp

import Core.TT
import Core.Context

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
     IPi : annot -> PiInfo -> Name -> 
           (argTy : RawImp annot) -> (retTy : RawImp annot) -> RawImp annot
     ILam : annot -> Name -> 
            (argTy : RawImp annot) -> (scope : RawImp annot) -> RawImp annot
     ILet : annot -> Name -> 
            (nTy : RawImp annot) -> (nVal : RawImp annot) -> 
            (scope : RawImp annot) ->
            RawImp annot
     IApp : annot -> 
            (fn : RawImp annot) -> (arg : RawImp annot) -> RawImp annot
     IPrimVal : annot -> Constant -> RawImp annot
     IType : annot -> RawImp annot
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
  show (ILam _ n argTy scope) 
      = "(%lam (" ++ show n ++ " " ++ show argTy ++ ") " 
             ++ show scope ++ ")"
  show (ILet _ n nTy nVal scope)
      = "(%let (" ++ show n ++ " " ++ show nTy ++ " " ++ show nVal ++ ") "
             ++ show scope ++ ")"
  show (IApp _ fn arg) 
      = "(" ++ show fn ++ " " ++ show arg ++ ")"
  show (IPrimVal _ y) = show y
  show (IType _) = "Type"
  show (Implicit _) = "_"

export
getAnnot : RawImp a -> a
getAnnot (IVar x _) = x
getAnnot (IPi x _ _ _ _) = x
getAnnot (ILam x _ _ _) = x
getAnnot (ILet x _ _ _ _) = x
getAnnot (IApp x _ _) = x
getAnnot (IPrimVal x _) = x
getAnnot (IType x) = x
getAnnot (Implicit x) = x

export
apply : RawImp a -> List (RawImp a) -> RawImp a
apply f [] = f
apply f (x :: xs) = apply (IApp (getAnnot f) f x) xs

