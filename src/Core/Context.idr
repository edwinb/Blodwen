module Core.Context

import Core.TT
import Core.CaseTree

import Data.SortedMap
import Data.List

%default total

export
data Context : Type -> Type where
     MkContext : SortedMap Name a -> Context a

export
empty : Context a
empty = MkContext empty

export
lookupCtxt : Name -> Context a -> Maybe a
lookupCtxt n (MkContext dict) = lookup n dict

export
addCtxt : Name -> a -> Context a -> Context a
addCtxt n val (MkContext dict) = MkContext (insert n val dict)

public export
data Def : Type where
     None  : Def -- Not yet defined
     PMDef : (args : List Name) -> CaseTree args -> Def
     DCon  : (tag : Int) -> (arity : Nat) -> Def
     TCon  : (tag : Int) -> (arity : Nat) -> Def

public export
data Visibility = Public | Export | Private

public export
record GlobalDef where
     constructor MkGlobalDef
     type : ClosedTerm
     visibility : Visibility
     definition : Def

-- A context of global definitions
public export
Gamma : Type
Gamma = Context GlobalDef

export
lookupDef : Name -> Gamma -> Maybe Def
lookupDef n gam = do def <- lookupCtxt n gam
                     pure (definition def)

export
lookupDefTy : Name -> Gamma -> Maybe (Def, ClosedTerm)
lookupDefTy n gam = do def <- lookupCtxt n gam
                       pure (definition def, type def)

export
plusDef : GlobalDef
plusDef = MkGlobalDef TType Public
           (PMDef [UN "x", UN "y"]
                  (testPlus (UN "plus")))

zDef : GlobalDef
zDef = MkGlobalDef TType Public
           (DCon 0 0)

sDef : GlobalDef
sDef = MkGlobalDef TType Public
           (DCon 1 1)

export
testGam : Gamma
testGam = addCtxt (UN "plus") plusDef $
          addCtxt (UN "Z") zDef $
          addCtxt (UN "S") sDef $
          empty

export
zero : Term sc
zero = Ref (DataCon 0 0) (UN "Z")

export
succ : Term sc
succ = Ref (DataCon 1 1) (UN "S")

export
one : Term sc
one = App succ zero

export
two : Term sc
two = App succ one

export
lam : (x : String) -> Term sc -> Term (UN x :: sc) -> Term sc
lam x ty tm = Bind (UN x) (Lam ty) tm

var : (x : String) -> {auto prf : Elem (UN x) sc} -> Term sc
var x {prf} = Local prf

idFn : Term []
idFn = lam "X" TType (lam "x" (var "X") (var "X"))
