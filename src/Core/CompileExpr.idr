-- Representation of expressions ready for compiling
-- Type erased, explicit case trees
module Core.CompileExpr

import Core.Name
import Core.TT

import Data.List
import Data.Vect

%default total

mutual
  public export
  data CExp : List Name -> Type where
       CLocal : Elem x vars -> CExp vars
       CRef : Name -> CExp vars
       CLam : (x : Name) -> CExp (x :: vars) -> CExp vars
       CLet : (x : Name) -> CExp vars -> CExp (x :: vars) -> CExp vars
       CApp : CExp vars -> List (CExp vars) -> CExp vars
       -- Internally defined primitive operations
       COp : PrimFn arity -> Vect arity (CExp vars) -> CExp vars
       -- Externally defined primitive operations
       CExtPrim : (p : Name) -> List (CExp vars) -> CExp vars
       CCase : (sc : CExp vars) -> List (CAlt vars) -> CExp vars
       CPrimVal : Constant -> CExp vars
       CErased : CExp vars

  public export
  data CAlt : List Name -> Type where
       CConCase : Name -> (tag : Int) -> (args : List Name) ->
                  CExp (args ++ vars) -> CAlt vars
       CConstCase : Constant -> CExp vars -> CAlt vars
       CDefaultCase : CExp vars -> CAlt vars
