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
       -- Application of a defined function. The length of the argument list is
       -- exactly the same length as expected by its definition (so saturate with
       -- lambdas if necessary, or overapply with additional CApps)
       CApp : CExp vars -> List (CExp vars) -> CExp vars
       -- A saturated constructor application
       CCon : Name -> (tag : Int) -> List (CExp vars) -> CExp vars
       -- Internally defined primitive operations
       COp : PrimFn arity -> Vect arity (CExp vars) -> CExp vars
       -- Externally defined primitive operations
       CExtPrim : (p : Name) -> List (CExp vars) -> CExp vars
       CCase : (sc : CExp vars) -> List (CAlt vars) -> CExp vars
       CPrimVal : Constant -> CExp vars
       CErased : CExp vars
       CCrash : String -> CExp vars

  public export
  data CAlt : List Name -> Type where
       CConCase : Name -> (tag : Int) -> (args : List Name) ->
                  CExp (args ++ vars) -> CAlt vars
       CConstCase : Constant -> CExp vars -> CAlt vars
       CDefaultCase : CExp vars -> CAlt vars

public export
data CDef : Type where
     -- Normal function definition
     MkFun : (args : List Name) -> CExp args -> CDef
     -- A function which will fail at runtime (usually due to being a hole) so needs
     -- to run, discarding arguments, no matter how many arguments are passed
     MkError : CExp [] -> CDef

mutual
  export 
  Show (CExp vars) where
    show (CLocal {x} y) = "!" ++ show x
    show (CRef x) = show x
    show (CLam x y) = "(lam " ++ show x ++ " " ++ show y ++ ")"
    show (CLet x y z) = "(let " ++ show x ++ " " ++ show y ++ " " ++ show z ++ ")"
    show (CApp x xs) 
        = assert_total $ "(" ++ show x ++ " " ++ show xs ++ ")"
    show (CCon x tag xs) 
        = assert_total $ "(con " ++ show x ++ " " ++ show tag ++ " " ++ show xs ++ ")"
    show (COp op xs) 
        = assert_total $ "(" ++ show op ++ " " ++ show xs ++ ")"
    show (CExtPrim p xs) 
        = assert_total $ "(%" ++ show p ++ " " ++ show xs ++ ")"
    show (CCase sc xs) 
        = assert_total $ "(case " ++ show sc ++ " " ++ show xs ++ ")"
    show (CPrimVal x) = show x
    show CErased = "___"
    show (CCrash x) = "(CRASH " ++ show x ++ ")"

  export 
  Show (CAlt vars) where
    show (CConCase x tag args exp)
         = "(concase " ++ show x ++ " " ++ show tag ++ " " ++
             show args ++ " " ++ show exp ++ ")"
    show (CConstCase x exp) 
         = "(constcase " ++ show x ++ " " ++ show exp ++ ")"
    show (CDefaultCase exp) 
         = "(defaultcase " ++ show exp ++ ")"

export
Show CDef where
  show (MkFun args exp) = show args ++ ": " ++ show exp
  show (MkError exp) = "Error: " ++ show exp
