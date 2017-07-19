module TTImp.TTImp

import Core.TT
import Core.Context

import Data.List

-- Unchecked terms, with implicit arguments
-- This is the raw, elaboratable form.
-- Higher level expressions (e.g. case, pattern matching let, where blocks,
-- do notation, etc, should elaborate via this, perhaps in some local 
-- context).
public export
data RawImp : Type where
     IVar : Name -> RawImp
     IPi : PiInfo -> Name -> 
           (argTy : RawImp) -> (retTy : RawImp) -> RawImp
     ILam : Name -> (argTy : RawImp) -> (scope : RawImp) -> RawImp
     ILet : Name -> 
            (nTy : RawImp) -> (nVal : RawImp) -> (scope : RawImp) ->
            RawImp
     IApp : (fn : RawImp) -> (arg : RawImp) -> RawImp
     IPrimVal : Constant -> RawImp
     Implicit : RawImp
-- TODO: IDotted (things which must be solved by inference and checked
-- against what's given)

export
apply : RawImp -> List RawImp -> RawImp
apply f [] = f
apply f (x :: xs) = apply (IApp f x) xs

