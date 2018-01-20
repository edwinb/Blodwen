module Idris.Syntax

import public Core.Core
import public Core.TT
import public Core.Binary

%hide Elab.Fixity

public export
FilePos : Type
FilePos = (Int, Int)

public export
FileName : Type
FileName = String

public export
record FC where
  constructor MkFC
  file : FileName
  startPos : FilePos
  endPos : FilePos

%name FC fc

export
TTC FC FC where
  toBuf b (MkFC fl st end)
      = do toBuf b fl
           toBuf b st
           toBuf b end

  fromBuf s b
      = do fl <- fromBuf s b
           st <- fromBuf s b
           end <- fromBuf s b
           pure (MkFC fl st end)

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
  data Directive : Type where
       Logging : Nat -> Directive

  public export
  data PDecl : Type where
       PClaim : FC -> PTypeDecl -> PDecl
       PDef : FC -> Name -> List PClause -> PDecl
       PData : FC -> PDataDecl -> PDecl
       PInfix : FC -> Fixity -> Nat -> Name -> PDecl
       PDirective : FC -> Directive -> PDecl

public export
data REPLCmd : Type where
     Eval : PTerm -> REPLCmd
     Check : PTerm -> REPLCmd
     ProofSearch : Name -> REPLCmd
     DebugInfo : Name -> REPLCmd
     Quit : REPLCmd

public export
record Module where
  constructor MkModule
  moduleNS : List String
  imports : List (List String)
  decls : List PDecl

