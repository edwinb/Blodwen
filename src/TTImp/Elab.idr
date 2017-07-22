module TTImp.Elab

import TTImp.TTImp
import Core.Context
import Core.TT
import Core.Unify

import public Control.ST
import public Control.ST.Exception

public export
data InferError : Type -> Type where
     GenericMsg : annot -> String -> InferError annot

export
interface (Exception m (InferError annot), ConsoleIO m) =>
          InferCtxt (m : Type -> Type) annot where

export
(Exception m (InferError annot), ConsoleIO m) => InferCtxt m annot where

check : InferCtxt m annot =>
        (ctxt : Var) -> Env Term vars ->
        (term : RawImp annot) -> (expected : Term vars) ->
        ST m (Term vars) [ctxt ::: Defs]
 
