module Unify

import Core.TT
import Core.Context
import Core.Evaluate

import Data.List
import public Control.ST

%default covering

-- Attempt to unify two values.
-- Throw an exception on failure - just a generic message since it will be
-- reported in terms of the higher level expressions being unified rather
-- than the values themselves.
uvals : CtxtManage m =>
        (ctxt : Var) -> Env Term vars ->
        Value vars -> Value vars -> ST m (List Name) [ctxt ::: Defs]
{-
uvals ctxt env (VLocal p) (VLocal q) 
    = if sameVar p q 
         then pure [] 
         else throw (GenericMsg "Can't unify variables")
uvals ctxt env (VBind x (Pi _ tx) scx) (VBind y (Pi _ ty) scy)
    = ?uvals_rhs_10
uvals ctxt env (VBind x bx scx) (VBind y by scy)
    = ?uvals_rhs_2
uvals ctxt env (VApp val thunk) val2 = ?uvals_rhs_3
uvals ctxt env (VPrimVal x) val2 = ?uvals_rhs_4
uvals ctxt env (VRef nt x) val2 = ?uvals_rhs_5
uvals ctxt env (VDCon x tag arity xs) val2 = ?uvals_rhs_6
uvals ctxt env (VTCon x tag arity xs) val2 = ?uvals_rhs_7
uvals ctxt env VErased val2 = ?uvals_rhs_8
uvals ctxt env VType val2 = ?uvals_rhs_9
uvals ctxt env x y = ?nomatch
-}

export
unify : CtxtManage m =>
        (ctxt : Var) -> Env Term vars ->
        Term vars -> Term vars -> ST m (List Name) [ctxt ::: Defs]
unify ctxt env x y 
    = do gam <- getCtxt ctxt
         uvals ctxt env (whnf gam env x) (whnf gam env y)
