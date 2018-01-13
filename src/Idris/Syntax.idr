module Idris.Syntax

import public Core.TT

%hide Elab.Fixity

public export
FilePos : Type
FilePos = (Int, Int)

public export
record FC where
  constructor MkFC
  file : String
  startPos : FilePos
  endPos : FilePos

public export
data Fixity = InfixL | InfixR | Infix

mutual
  -- The full high level source language
  -- This gets desugared to RawImp (TTImp.TTImp), then elaborated to 
  -- Term (Core.TT)
  public export
  data PTerm : Type where
       PRef : FC -> Name -> PTerm
       PPi : FC -> PiInfo -> Maybe Name -> 
             (argTy : PTerm) -> (retTy : PTerm) -> PTerm
       PLam : FC -> PiInfo -> Name ->
              (argTy : PTerm) -> (scope : PTerm) -> PTerm
       PLet : FC -> Name ->
              (nTy : PTerm) -> (nVal : PTerm) -> (scope : PTerm) -> PTerm
       PCase : FC -> PTerm -> List PClause -> PTerm
       PLocal : FC -> List PDecl -> (scope : PTerm) -> PTerm
       PApp : FC -> PTerm -> PTerm -> PTerm
       PImplicitApp : FC -> PTerm -> (argn : Name) -> PTerm -> PTerm
       PSearch : FC -> (depth : Nat) -> PTerm
       PPrimVal : FC -> Constant -> PTerm
       PHole : FC -> (holename : String) -> PTerm
       PType : FC -> PTerm
       PAs : FC -> (vname : String) -> (pattern : PTerm) -> PTerm
       PDotted : FC -> PTerm -> PTerm
       PImplicit : FC -> PTerm

  public export
  data PTypeDecl : Type where
       MkPTy : FC -> (n : Name) -> (type : PTerm) -> PTypeDecl

  public export
  data PDataDecl : Type where
       MkPData : FC -> (tyname : Name) -> (tycon : PTerm) ->
                 (datacons : List PTypeDecl) -> PDataDecl

  public export
  data PClause : Type where
       MkPatClause : FC -> (lhs : PTerm) -> (rhs : PTerm) -> PClause
       MkImpossible : FC -> (lhs : PTerm) -> PClause

  public export
  data PDecl : Type where
       PClaim : FC -> PTypeDecl -> PDecl
       PDef : FC -> Name -> List PClause -> PDecl
       PData : FC -> PDataDecl -> PDecl
       PInfix : FC -> Fixity -> Nat -> Name -> PDecl
       
