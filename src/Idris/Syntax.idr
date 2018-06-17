module Idris.Syntax

import public Core.Binary
import public Core.Context
import public Core.Core
import public Core.Normalise
import public Core.Reflect
import public Core.TTC
import public Core.TT

import TTImp.Reflect
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
Reify FC where
  reify defs (NDCon (NS _ (UN "MkFC")) _ _ [file, start, end])
      = do file' <- reify defs (evalClosure defs file)
           start' <- reify defs (evalClosure defs start)
           end' <- reify defs (evalClosure defs end)
           pure (MkFC file' start' end')
  reify defs _ = Nothing

export
Reflect FC where
  reflect defs env fc
      = do file' <- reflect defs env (file fc)
           start' <- reflect defs env (startPos fc)
           end' <- reflect defs env (endPos fc)
           appCon defs (NS ["Reflect"] (UN "MkFC")) [file', start', end']

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
       PLet : FC -> RigCount -> (pat : PTerm) -> 
              (nTy : PTerm) -> (nVal : PTerm) -> (scope : PTerm) -> 
              (alts : List PClause) -> PTerm
       PCase : FC -> PTerm -> List PClause -> PTerm
       PLocal : FC -> List PDecl -> (scope : PTerm) -> PTerm
       PApp : FC -> PTerm -> PTerm -> PTerm
       PImplicitApp : FC -> PTerm -> (argn : Name) -> PTerm -> PTerm
       PSearch : FC -> (depth : Nat) -> PTerm
       PPrimVal : FC -> Constant -> PTerm
       PQuote : FC -> PTerm -> PTerm
       PUnquote : FC -> PTerm -> PTerm
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
       PEq : FC -> PTerm -> PTerm -> PTerm
       PBracketed : FC -> PTerm -> PTerm

       -- Syntactic sugar
       
       PDoBlock : FC -> List PDo -> PTerm
       PList : FC -> List PTerm -> PTerm
       PPair : FC -> PTerm -> PTerm -> PTerm
       PUnit : FC -> PTerm
       PIfThenElse : FC -> PTerm -> PTerm -> PTerm -> PTerm

       -- TODO: Dependent pairs, enumerations, idiom brackets, 
       -- comprehensions, rewrites

  public export
  data PDo : Type where
       DoExp : FC -> PTerm -> PDo
       DoBind : FC -> Name -> PTerm -> PDo
       DoBindPat : FC -> PTerm -> PTerm -> List PClause -> PDo
       DoLet : FC -> Name -> RigCount -> PTerm -> PDo
       DoLetPat : FC -> PTerm -> PTerm -> List PClause -> PDo
       DoLetLocal : FC -> List PDecl -> PDo

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
       MkPLater : FC -> (tyname : Name) -> (tycon : PTerm) -> PDataDecl

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
       PInterface : FC -> 
                    Visibility ->
                    (constraints : List (Maybe Name, PTerm)) ->
                    Name ->
                    (params : List (Name, PTerm)) ->
                    (det : List Name) ->
                    (conName : Maybe Name) ->
                    List PDecl ->
                    PDecl
       PImplementation : FC ->
                         Visibility ->
                         (constraints : List (Maybe Name, PTerm)) ->
                         Name ->
                         (params : List PTerm) ->
                         (implName : Maybe Name) ->
                         List PDecl ->
                         PDecl
       -- TODO: PRecord
       -- TODO: PPostulate
       -- TODO: PMutual
       -- TODO: POpen (for opening named interfaces)
       PFixity : FC -> Fixity -> Nat -> OpStr -> PDecl
       PNamespace : FC -> List String -> List PDecl -> PDecl
       PDirective : FC -> Directive -> PDecl

public export
data REPLEval : Type where
     EvalTC : REPLEval -- Evaluate as if part of the typechecker
     NormaliseAll : REPLEval -- Normalise everything (default)
     Execute : REPLEval -- Evaluate then pass to an executer

public export
data REPLOpt : Type where
     ShowImplicits : Bool -> REPLOpt
     ShowTypes : Bool -> REPLOpt
     EvalMode : REPLEval -> REPLOpt

public export
data REPLCmd : Type where
     Eval : PTerm -> REPLCmd
     Check : PTerm -> REPLCmd
     ProofSearch : Name -> REPLCmd
     DebugInfo : Name -> REPLCmd
     SetOpt : REPLOpt -> REPLCmd
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

showCount : RigCount -> String
showCount Rig0 = "0 "
showCount Rig1 = "1 "
showCount RigW = ""

export
Show PTerm where
  show (PRef _ n) = show n
  show (PPi _ rig Explicit Nothing arg ret)
      = show arg ++ " -> " ++ show ret
  show (PPi _ rig Explicit (Just n) arg ret)
      = "(" ++ showCount rig ++ show n ++ " : " ++ show arg ++ ") -> " ++ show ret
  show (PPi _ rig Implicit Nothing arg ret) -- shouldn't happen
      = "{" ++ showCount rig ++ "_ : " ++ show arg ++ "} -> " ++ show ret
  show (PPi _ rig Implicit (Just n) arg ret)
      = "{" ++ showCount rig ++ show n ++ " : " ++ show arg ++ "} -> " ++ show ret
  show (PPi _ rig AutoImplicit Nothing arg ret) -- shouldn't happen
      = "{auto " ++ showCount rig ++ "_ : " ++ show arg ++ "} -> " ++ show ret
  show (PPi _ rig AutoImplicit (Just n) arg ret)
      = "{auto " ++ showCount rig ++ show n ++ " : " ++ show arg ++ "} -> " ++ show ret
  show (PLam _ rig _ n (PImplicit _) sc)
      = "\\" ++ showCount rig ++ show n ++ " => " ++ show sc
  show (PLam _ rig _ n ty sc)
      = "\\" ++ showCount rig ++ show n ++ " : " ++ show ty ++ " => " ++ show sc
  show (PLet _ rig n (PImplicit _) val sc alts)
      = "let " ++ showCount rig ++ show n ++ " = " ++ show val ++ " in " ++ show sc
  show (PLet _ rig n ty val sc alts)
      = "let " ++ showCount rig ++ show n ++ " : " ++ show ty ++ " = " 
               ++ show val ++ concatMap showAlt alts ++
               " in " ++ show sc
    where
      showAlt : PClause -> String
      showAlt (MkPatClause _ lhs rhs _) = " | " ++ show lhs ++ " => " ++ show rhs ++ ";"
      showAlt (MkImpossible _ lhs) = " | " ++ show lhs ++ " impossible;"
  show (PCase _ tm cs) 
      = "case " ++ show tm ++ " of { " ++ 
          showSep " ; " (map showCase cs) ++ " }"
    where
      showCase : PClause -> String
      showCase (MkPatClause _ lhs rhs _) = show lhs ++ " => " ++ show rhs
      showCase (MkImpossible _ lhs) = show lhs ++ " impossible"
  show (PLocal _ ds sc) -- We'll never see this when displaying a normal form...
      = "let { << definitions >>  } in " ++ show sc
  show (PApp _ f a) = show f ++ " " ++ show a
  show (PImplicitApp _ f n (PRef _ a)) 
      = if n == a
           then show f ++ " {" ++ show n ++ "}"
           else show f ++ " {" ++ show n ++ " = " ++ show a ++ "}"
  show (PImplicitApp _ f n a) 
      = show f ++ " {" ++ show n ++ " = " ++ show a ++ "}"
  show (PSearch _ d) = "%search"
  show (PQuote _ tm) = "`(" ++ show tm ++ ")"
  show (PUnquote _ tm) = "~(" ++ show tm ++ ")"
  show (PPrimVal _ c) = show c
  show (PHole _ n) = "?" ++ n
  show (PType _) = "Type"
  show (PAs _ n p) = n ++ "@" ++ show p
  show (PDotted _ p) = "." ++ show p
  show (PImplicit _) = "_"
  show (POp _ op x y) = show x ++ " " ++ op ++ " " ++ show y
  show (PPrefixOp _ op x) = op ++ show x
  show (PSectionL _ op x) = "(" ++ op ++ " " ++ show x ++ ")"
  show (PSectionR _ x op) = "(" ++ show x ++ " " ++ op ++ ")"
  show (PEq fc l r) = show l ++ " = " ++ show r
  show (PBracketed _ tm) = "(" ++ show tm ++ ")"
  show (PDoBlock _ ds) 
      = "do " ++ showSep " ; " (map showDo ds)
    where
      showAlt : PClause -> String
      showAlt (MkPatClause _ lhs rhs _) = " | " ++ show lhs ++ " => " ++ show rhs ++ ";"
      showAlt (MkImpossible _ lhs) = " | " ++ show lhs ++ " impossible;"

      showDo : PDo -> String
      showDo (DoExp _ tm) = show tm
      showDo (DoBind _ n tm) = show n ++ " <- " ++ show tm
      showDo (DoBindPat _ l tm alts) 
          = show l ++ " <- " ++ show tm ++ concatMap showAlt alts
      showDo (DoLet _ l rig tm) = "let " ++ show l ++ " = " ++ show tm
      showDo (DoLetPat _ l tm alts) 
          = "let " ++ show l ++ " = " ++ show tm ++ concatMap showAlt alts
  show (PList _ xs)
      = "[" ++ showSep ", " (map show xs) ++ "]"
  show (PPair _ l r) = "(" ++ show l ++ ", " ++ show r ++ ")"
  show (PUnit _) = "()"
  show (PIfThenElse _ x t e) = "if " ++ show x ++ " then " ++ show t ++
                               " else " ++ show e

public export
record IFaceInfo where
  constructor MkIFaceInfo
  iconstructor : Name
  params : List Name
  methods : List (Name, RawImp FC) 
     -- ^ name and desugared type (without constraint)
  defaults : List (Name, ImpDecl FC)

export
TTC FC IFaceInfo where
  toBuf b (MkIFaceInfo ic ps ms ds)
      = do toBuf b ic
           toBuf b ps
           toBuf b ms
           toBuf b ds

  fromBuf s b
      = do ic <- fromBuf s b
           ps <- fromBuf s b
           ms <- fromBuf s b
           ds <- fromBuf s b
           pure (MkIFaceInfo ic ps ms ds)

public export
record SyntaxInfo where
  constructor MkSyntax
  -- Keep infix/prefix, then we can define operators which are both
  -- (most obviously, -)
  infixes : StringMap (Fixity, Nat)
  prefixes : StringMap Nat
  ifaces : Context IFaceInfo

export
TTC annot Fixity where
  toBuf b InfixL = tag 0
  toBuf b InfixR = tag 1
  toBuf b Infix = tag 2
  toBuf b Prefix = tag 3

  fromBuf s b 
      = case !getTag of
             0 => pure InfixL
             1 => pure InfixR
             2 => pure Infix
             3 => pure Prefix
             _ => corrupt "Fixity"

export
TTC FC SyntaxInfo where
  toBuf b syn 
      = do toBuf b (toList (infixes syn))
           toBuf b (toList (prefixes syn))
           toBuf b (ifaces syn) 

  fromBuf s b 
      = do inf <- fromBuf s b
           pre <- fromBuf s b
           ifs <- fromBuf s b
           pure (MkSyntax (fromList inf) (fromList pre) ifs)

export
initSyntax : SyntaxInfo
initSyntax = MkSyntax empty empty empty

-- A label for Syntax info in the global state
export
data Syn : Type where

