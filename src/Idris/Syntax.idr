module Idris.Syntax

import public Core.Context
import public Core.Core
import public Core.TT
import public Core.Binary

import TTImp.TTImp

%hide Elab.Fixity

public export
FilePos : Type
FilePos = (Int, Int)

showPos : FilePos -> String
showPos (l, c) = show (l + 1) ++ ":" ++ show (c + 1)

public export
FileName : Type
FileName = String

public export
record FC where
  constructor MkFC
  file : FileName
  startPos : FilePos
  endPos : FilePos

export
emptyFC : FC
emptyFC = MkFC "(no file)" (0, 0) (0, 0)

export
toplevelFC : FC
toplevelFC = MkFC "(toplevel)" (0, 0) (0, 0)

%name FC fc

export
Show FC where
  show loc = file loc ++ ":" ++ 
             showPos (startPos loc) ++ "--" ++ 
             showPos (endPos loc)

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
data Fixity = InfixL | InfixR | Infix | Prefix

public export
OpStr : Type
OpStr = String

mutual
  -- The full high level source language
  -- This gets desugared to RawImp (TTImp.TTImp), then elaborated to 
  -- Term (Core.TT)
  public export
  data PTerm : Type where
       -- Direct (more or less) translations to RawImp

       PRef : FC -> Name -> PTerm
       PPi : FC -> RigCount -> PiInfo -> Maybe Name -> 
             (argTy : PTerm) -> (retTy : PTerm) -> PTerm
       PLam : FC -> RigCount -> PiInfo -> Name ->
              (argTy : PTerm) -> (scope : PTerm) -> PTerm
       -- TODO: LHS should be pattern, and allow alternatives on RHS
       PLet : FC -> RigCount -> Name ->
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

       -- Operators

       POp : FC -> OpStr -> PTerm -> PTerm -> PTerm
       PPrefixOp : FC -> OpStr -> PTerm -> PTerm
       PSectionL : FC -> OpStr -> PTerm -> PTerm
       PSectionR : FC -> PTerm -> OpStr -> PTerm
       PBracketed : FC -> PTerm -> PTerm

       -- Syntactic sugar
       
       PDoBlock : FC -> List PDo -> PTerm
       PPair : FC -> PTerm -> PTerm -> PTerm
       PUnit : FC -> PTerm

       -- TODO: Dependent pairs, lists, idiom brackets, equality,
       -- comprehensions, if/then/else, rewrites

  public export
  data PDo : Type where
       DoExp : FC -> PTerm -> PDo
       DoBind : FC -> Name -> PTerm -> PDo
       DoBindPat : FC -> PTerm -> PTerm -> List PClause -> PDo
       DoLet : FC -> Name -> RigCount -> PTerm -> PDo
       DoLetPat : FC -> PTerm -> PTerm -> List PClause -> PDo

  export
  getLoc : PDo -> FC
  getLoc (DoExp fc _) = fc
  getLoc (DoBind fc _ _) = fc
  getLoc (DoBindPat fc _ _ _) = fc
  getLoc (DoLet fc _ _ _) = fc
  getLoc (DoLetPat fc _ _ _) = fc

  export
  papply : FC -> PTerm -> List PTerm -> PTerm
  papply fc f [] = f
  papply fc f (a :: as) = papply fc (PApp fc f a) as

  public export
  data PTypeDecl : Type where
       MkPTy : FC -> (n : Name) -> (type : PTerm) -> PTypeDecl

  public export
  data PDataDecl : Type where
       MkPData : FC -> (tyname : Name) -> (tycon : PTerm) ->
                 (opts : List DataOpt) ->
                 (datacons : List PTypeDecl) -> PDataDecl

  public export
  data PClause : Type where
       MkPatClause : FC -> (lhs : PTerm) -> (rhs : PTerm) -> 
                     (whereblock : List PDecl) -> PClause
       -- TODO: MkWithClause
       MkImpossible : FC -> (lhs : PTerm) -> PClause

  public export
  data Directive : Type where
       Logging : Nat -> Directive
       LazyNames : Name -> Name -> Name -> Directive

  public export
  data PDecl : Type where
       PClaim : FC -> Visibility -> List FnOpt -> PTypeDecl -> PDecl
       PDef : FC -> Name -> List PClause -> PDecl
       PData : FC -> Visibility -> PDataDecl -> PDecl
       PReflect : FC -> PTerm -> PDecl
       -- TODO: PRecord
       -- TODO: PInterface
       -- TODO: PImplementation
       -- TODO: PPostulate
       -- TODO: POpen (for opening named interfaces)
       PFixity : FC -> Fixity -> Nat -> OpStr -> PDecl
       PNamespace : FC -> List String -> List PDecl -> PDecl
       PDirective : FC -> Directive -> PDecl

public export
data REPLCmd : Type where
     Eval : PTerm -> REPLCmd
     Check : PTerm -> REPLCmd
     ProofSearch : Name -> REPLCmd
     DebugInfo : Name -> REPLCmd
     Quit : REPLCmd

public export
record Import where
  constructor MkImport
  loc : FC
  reexport : Bool
  path : List String
  nameAs : List String

public export
record Module where
  constructor MkModule
  headerloc : FC
  moduleNS : List String
  imports : List Import
  decls : List PDecl

