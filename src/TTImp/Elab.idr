module TTImp.Elab

import TTImp.TTImp
import Core.Context
import Core.TT
import Core.Unify

import public Control.ST
import public Control.ST.Exception

public export
data InferError : Type -> Type where
     CoreError : annot -> Error -> InferError annot
     CantUnify : annot -> Env Term vars -> Term vars -> Term vars ->
                 InferError annot
     GenericMsg : annot -> String -> InferError annot

export
interface (Exception m (InferError annot), CtxtManage m) =>
          InferCtxt (m : Type -> Type) annot where

export
(Exception m (InferError annot), CtxtManage m) => InferCtxt m annot where

convert : InferCtxt m annot => 
          (ctxt : Var) -> annot ->
          Env Term vars ->
          Term vars -> Term vars -> ST m (List Name) [ctxt ::: Defs]
convert ctxt loc env x y 
    = catch (unify ctxt env x y)
            (\_ => throw (CantUnify loc env x y))

check : InferCtxt m annot =>
        (ctxt : Var) -> Env Term vars ->
        (term : RawImp annot) -> (expected : Term vars) ->
        ST m (Term vars) [ctxt ::: Defs]
 
