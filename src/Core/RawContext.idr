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

addTyDecl : {auto c : Ref Ctxt Defs} ->
            annot -> (ty : RawTy) -> Core annot (Name, ClosedTerm)
addTyDecl loc (MkRawTy n ty)
    = do tyc <- check loc [] ty TType
         addDef n (newDef tyc Public None)
         pure (n, tyc)

checkClause : {auto c : Ref Ctxt Defs} ->
              annot -> RawClause -> Core annot Clause
checkClause loc (MkRawClause pvars lhs rhs)
-- Plan: Check the LHS, extract the environment, use that to check the RHS,
-- then make sure the types of each side are convertible.
    = do let lhs_in = bind pvars lhs
         -- TODO: Logging here instead
         -- putStrLn ("Checking LHS " ++ show lhs_in)
         (lhsc, lhsty) <- infer loc [] lhs_in
         let (patvars ** (lhsenv, lhsbound, lhsboundty)) 
              = getPatternEnv [] lhsc lhsty
         -- putStrLn ("Checking RHS " ++ show rhs)
         (rhsc, rhsty) <- infer loc lhsenv rhs
         checkConvert loc lhsenv lhsboundty rhsty
         pure (MkClause lhsenv lhsbound rhsc)
  where
    bind : List (Name, Raw) -> Raw -> Raw
    bind [] tm = tm
    bind ((n, ty) :: ps) tm = RBind n (PVar ty) (bind ps tm)

addFn : {auto c : Ref Ctxt Defs} ->
        annot -> (def : RawFnDef) -> Core annot ()
addFn loc (MkRawFn n ty cs)
    = do tyc <- check loc [] ty TType
         addDef n (newDef tyc Public None)
         csc <- traverse (\x => checkClause loc x) cs
         addFnDef loc Public (MkFn n tyc csc)

addData : {auto c : Ref Ctxt Defs} ->
          annot -> (def : RawData) -> Core annot ()
addData loc (MkRawData tycon datacons)
    = do (tn, tty) <- addTyDecl loc tycon
         cons <- traverse (\x => checkCon x) datacons
         gam <- getCtxt 
         let def = MkData (MkCon tn (getArity gam [] tty) tty) cons
         addData Public def
  where
    checkCon : RawTy -> Core annot Constructor
    checkCon (MkRawTy n ty) 
        = do tyc <- check loc [] ty TType
             gam <- getCtxt 
             pure (MkCon n (getArity gam [] tyc) tyc)

export
addDecl : {auto c : Ref Ctxt Defs} ->
          annot -> (def : RawDecl) -> Core annot ()
addDecl loc (FnDecl f) = addFn loc f
addDecl loc (DataDecl d) = addData loc d
