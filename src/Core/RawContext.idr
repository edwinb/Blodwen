module Core.RawContext

import Core.Context
import Core.Typecheck
import Core.Normalise
import Core.TT

%default covering

public export
data RawTy : Type where
     MkRawTy : (n : Name) -> (ty : Raw) -> RawTy

public export
data RawData : Type where
     MkRawData : (tycon : RawTy) -> (datacons : List RawTy) -> RawData

public export
data RawClause : Type where
     MkRawClause : (pvars : List (Name, Raw)) ->
                   (lhs : Raw) -> (rhs : Raw) -> RawClause

public export
data RawFnDef : Type where
     MkRawFn : (n : Name) -> (ty : Raw) -> (clauses : List RawClause) ->
               RawFnDef

public export
data RawDecl = FnDecl RawFnDef
             | DataDecl RawData

using (CtxtManage m)
  addTyDecl : (ctxt : Var) -> (ty : RawTy) -> 
              ST m (Name, ClosedTerm) [ctxt ::: Defs]
  addTyDecl ctxt (MkRawTy n ty)
      = do tyc <- check ctxt [] ty TType
           addDef ctxt n (MkGlobalDef tyc Public None)
           pure (n, tyc)

  checkClause : (ctxt : Var) -> RawClause -> ST m Clause [ctxt ::: Defs]
  checkClause ctxt (MkRawClause pvars lhs rhs)
  -- Plan: Check the LHS, extract the environment, use that to check the RHS,
  -- then make sure the types of each side are convertible.
      = do let lhs_in = bind pvars lhs
           putStrLn ("Checking LHS " ++ show lhs_in)
           (lhsc, lhsty) <- infer ctxt [] lhs_in
           let (patvars ** (lhsenv, lhsbound, lhsboundty)) 
                = getPatternEnv [] lhsc lhsty
           putStrLn ("Checking RHS " ++ show rhs)
           (rhsc, rhsty) <- infer ctxt lhsenv rhs
           checkConvert ctxt lhsenv lhsboundty rhsty
           pure (MkClause lhsenv lhsbound rhsc)
    where
      bind : List (Name, Raw) -> Raw -> Raw
      bind [] tm = tm
      bind ((n, ty) :: ps) tm = RBind n (PVar ty) (bind ps tm)

  addFn : (ctxt : Var) -> (def : RawFnDef) -> ST m () [ctxt ::: Defs]
  addFn ctxt (MkRawFn n ty cs)
      = do tyc <- check ctxt [] ty TType
           addDef ctxt n (MkGlobalDef tyc Public None)
           csc <- mapST (checkClause ctxt) cs
           addFnDef ctxt Public (MkFn n tyc csc)

  addData : (ctxt : Var) -> (def : RawData) -> ST m () [ctxt ::: Defs]
  addData ctxt (MkRawData tycon datacons)
      = do (tn, tty) <- addTyDecl ctxt tycon
           cons <- mapST checkCon datacons
           gam <- getCtxt ctxt
           let def = MkData (MkCon tn (getArity gam [] tty) tty) cons
           addData ctxt Public def
    where
      checkCon : RawTy -> ST m Constructor [ctxt ::: Defs]
      checkCon (MkRawTy n ty) 
          = do tyc <- check ctxt [] ty TType
               gam <- getCtxt ctxt
               pure (MkCon n (getArity gam [] tyc) tyc)

  export
  addDecl : (ctxt : Var) -> (def : RawDecl) -> ST m () [ctxt ::: Defs]
  addDecl ctxt (FnDecl f) = addFn ctxt f
  addDecl ctxt (DataDecl d) = addData ctxt d
