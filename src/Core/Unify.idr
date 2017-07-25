module Unify

import Core.TT
import Core.Context
import Core.Evaluate

import Data.List
import Control.ST
import Control.ST.ImplicitCall

%default covering

public export
data Constraint : Type where
     -- An unsolved constraint, noting two terms which need to be convertible
     -- in a particular environment
     MkConstraint : (env : Env Term vars) ->
                    (x : Term vars) -> (y : Term vars) -> 
                    Constraint
     -- An unsolved sequence of constraints, arising from arguments in an
     -- application where solving later constraints relies on solving earlier
     -- ones
     MkSeqConstraint : (env : Env Term vars) ->
                       (x : List (Closure vars)) ->
                       (y : List (Closure vars)) ->
                       Constraint
     -- a previously resolved constraint
     Resolved : Constraint 

-- union : List Name -> List Name -> List Name
-- union cs cs' = nub (cs ++ cs') -- TODO: as a set, not list

-- Currently unsolved constraints - the 'constraints' in the 'Guess'
-- definitions in Gamma refer into this unification state
export
record UnifyState where
     constructor MkUnifyState
     holes : List Name -- unsolved metavariables in gamma
     constraints : Context Constraint -- metavariable constraints 
     nextVar : Int -- next name for checking scopes of binders

initUState : UnifyState
initUState = MkUnifyState [] empty 0

export
UState : Type
UState = State UnifyState

genName : (ustate : Var) -> String -> ST m Name [ustate ::: UState]
genName ustate root
    = do ust <- read ustate
         write ustate (record { nextVar $= (+1) } ust)
         pure (MN root (nextVar ust))

export
addConstraint : CtxtManage m => 
                (ctxt : Var) -> (ustate : Var) ->
                Constraint ->        
                ST m Name [ctxt ::: Defs, ustate ::: UState]
addConstraint ctxt ustate constr
    = do c_id <- getNextHole ctxt
         let cn = MN "constraint" c_id
         ust <- read ustate
         write ustate (record { constraints = 
                                  addCtxt cn constr (constraints ust) } ust)
         pure cn

mkConstant : Env Term vars -> Term vars -> ClosedTerm
mkConstant [] tm = tm
mkConstant {vars = x :: _} (b :: env) tm 
    = let ty = binderType b in
          mkConstant env (Bind x (Lam ty) tm)

mkConstantTy : Env Term vars -> Term vars -> ClosedTerm
mkConstantTy [] tm = tm
mkConstantTy {vars = x :: _} (b :: env) tm 
    = let ty = binderType b in
          mkConstant env (Bind x (Pi Explicit ty) tm)

mkConstantAppArgs : Env Term vars -> 
                    List (Term done) -> List (Term (vars ++ done))
mkConstantAppArgs [] xs = xs
mkConstantAppArgs (b :: env) xs 
    = let rec = mkConstantAppArgs env xs in
          Local Here :: map weaken rec

-- Apply a constant to the current environment.
-- Leftmost argument is the outermost variable, so make a list of local
-- variables then reverse it
mkConstantApp : Name -> Env Term vars -> Term vars
mkConstantApp {vars} cn env 
  = let args = reverse (mkConstantAppArgs {done = []} env []) in
        apply (Ref Func cn) (rewrite sym (appendNilRightNeutral vars) in args)

export
addConstant : CtxtManage m =>
              (ctxt : Var) -> (ustate : Var) ->
              Env Term vars -> 
              (tm : Term vars) -> (ty : Term vars) ->
              (constrs : List Name) ->
              ST m Name [ctxt ::: Defs, ustate ::: UState]
addConstant ctxt ustate env tm ty constrs
    = do let def = mkConstant env tm
         let defty = mkConstantTy env ty
         let guess = MkGlobalDef defty Public (Guess def constrs)
         cn <- genName ustate "p"
         addDef ctxt cn guess
         pure cn


parameters (ctxt : Var, ustate : Var)

  export
  instantiate : CtxtManage m => 
                Env Term vars -> (x : Name) ->
                (Closure vars -> Closure vars) -> Term (x :: vars) ->
                ST m (Value (x :: vars)) [ctxt ::: Defs, ustate ::: UState]
  instantiate env x f tm 
      = do dummy <- genName ustate "scope"
           gam <- getCtxt ctxt
           let scope = refToLocal dummy x 
                  (quote env (f (MkClosure [] env (Ref Bound dummy))))
           ?foo

  mutual
    unifyArgs : CtxtManage m =>
                Env Term vars ->
                List (Closure vars) -> List (Closure vars) ->
                ST m (List Name) [ctxt ::: Defs, ustate ::: UState]
    unifyArgs env [] [] = pure []
    unifyArgs env (cx :: cxs) (cy :: cys)
        = do gam <- getCtxt ctxt
             let vx = evalClosure gam cx
             let vy = evalClosure gam cy
             constr <- uvals env vx vy
             case constr of
                  [] => unifyArgs env cxs cys
                  _ => do c <- addConstraint ctxt ustate 
                                 (MkSeqConstraint env (cx :: cxs) (cy :: cys))
                          pure [c]
    unifyArgs env _ _ = throw (GenericMsg "UnifyFail")

    unifyApp : CtxtManage m =>
               Env Term vars ->
               VHead vars -> List (Closure vars) -> Value vars ->
               ST m (List Name) [ctxt ::: Defs, ustate ::: UState]

    -- Attempt to unify two values.
    -- Throw an exception on failure - just a generic message since it will be
    -- reported in terms of the higher level expressions being unified rather
    -- than the values themselves.
    uvals : CtxtManage m =>
            Env Term vars ->
            Value vars -> Value vars -> 
            ST m (List Name) [ctxt ::: Defs, ustate ::: UState]
    uvals env (VBind x (Pi ix tx) fx) (VBind y (Pi iy ty) fy)
        = if ix /= iy 
             then throw (GenericMsg "Unify failure in plicity")
             else
              do gam <- getCtxt ctxt
                 ct <- uvals env (evalClosure gam tx)
                                 (evalClosure gam ty)
                 let env' : TT.Env.Env Term (x :: _) 
                          = Pi ix (quote env tx) :: env
                 case ct of
                      [] => -- no constraints, check the scopes
                            ?uvalsPi1
--                             uvals env' !(instantiate env x fx (Local Here))
--                                        !(instantiate env x fy (Local Here))
                      cs => -- constraints, so make new guarded constant
                          do ?uvalsPi2
--                              let txtm = quote env tx
--                              let tytm = quote env ty
--                              c <- addConstant ctxt ustate env 
--                                      (Bind x (Lam txtm) (Local Here))
--                                      (Bind x (Pi Explicit txtm) (weaken tytm))
--                                      cs
--                              let scy = mkConstantApp c env'
--                              cs' <- uvals env' 
--                                        !(instantiate env x fx (Local Here))
--                                        !(instantiate env x fy scy) 
--                              pure (union cs cs')
    uvals env (VBind x bx fx) (VBind y by fy)
        = ?uvals_rhs_1
    uvals env (VApp var args) val = unifyApp env var args val
    uvals env val (VApp var args) = unifyApp env var args val
    uvals env (VDCon x tagx arityx xs) (VDCon y tagy arityy ys)
        = if tagx == tagy
             then unifyArgs env xs ys
             else throw (GenericMsg "Unify failure")
    uvals env (VTCon x tagx arityx xs) (VTCon y tagy arityy ys)
        = if tagx == tagy
             then unifyArgs env xs ys
             else throw (GenericMsg "Unify failure")
    uvals env (VPrimVal x) (VPrimVal y) 
        = if x == y then pure []
                    else throw (GenericMsg "Unify failure")
    uvals env VErased _ = pure []
    uvals env _ VErased = pure []
    uvals env VType VType = pure []
    uvals env x y = throw (GenericMsg "Unify failure")

export
unify : CtxtManage m =>
        (ctxt : Var) -> (ustate : Var) ->
        Env Term vars -> Term vars -> Term vars -> 
        ST m (List Name) [ctxt ::: Defs, ustate ::: UState]
unify ctxt ustate env x y 
    = do gam <- getCtxt ctxt
         uvals ctxt ustate env (whnf gam env x) (whnf gam env y)

