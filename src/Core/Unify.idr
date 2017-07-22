module Unify

import Core.TT
import Core.Context

import public Control.ST

data UnifyResult = OK -- Succeeded (possibly solving metavariables) 
                 | Fail -- Couldn't unify
                 | NewConst Name -- Added a new guarded constant

unify : (ctxt : Var) -> Env Term vars ->
        Term vars -> Term vars -> ST m UnifyResult [ctxt ::: Defs]
