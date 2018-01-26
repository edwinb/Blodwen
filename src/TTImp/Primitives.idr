module TTImp.Primitives

import Core.Core
import Core.Context
import Core.TT

import Data.Vect

addOp : Vect 2 (NF vars) -> Maybe (NF vars)
addOp [NPrimVal (BI x), NPrimVal (BI y)] = Just (NPrimVal (BI (x + y)))
addOp _ = Nothing

export
addPrimitives : {auto c : Ref Ctxt Defs} -> Core annot ()
addPrimitives
    = do addBuiltin (UN "prim__add") 
                (PrimVal IntegerType `fnType` (PrimVal IntegerType `fnType`
                         PrimVal IntegerType))
                Total addOp


