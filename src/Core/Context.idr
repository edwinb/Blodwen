module Core.Context

import Core.TT
import Core.CaseTree

import public Control.ST
import public Control.ST.Exception

import Control.IOExcept
import Data.SortedMap
import Data.List

%default total

export
data Context : Type -> Type where
     MkContext : SortedMap Name a -> Context a

export
mapST : (a -> STrans m b cs (const cs)) -> List a ->
        STrans m (List b) cs (const cs)
mapST f [] = pure []
mapST f (x :: xs) 
    = do x' <- f x
         xs' <- mapST f xs
         pure (x' :: xs')

export
empty : Context a
empty = MkContext empty

export
lookupCtxt : Name -> Context a -> Maybe a
lookupCtxt n (MkContext dict) = lookup n dict

export
addCtxt : Name -> a -> Context a -> Context a
addCtxt n val (MkContext dict) = MkContext (insert n val dict)

-- An unsolved constraint, noting two terms which need to be convertible
-- in a particular environment
public export
data Constraint : Type where
     MkConstraint : (env : Env Term vars) ->
                    (x : Term vars) -> (y : Term vars) -> 
                    (ty : Maybe (Term vars)) -> Constraint

public export
data Def : Type where
     None  : Def -- Not yet defined
     PMDef : (args : List Name) -> CaseTree args -> Def
     DCon  : (tag : Int) -> (arity : Nat) -> Def
     TCon  : (tag : Int) -> (arity : Nat) -> (datacons : List Name) -> Def

     Hole : Def
     -- The constraint names refer into the context of constraints in Gamma
     Guess : (guess : ClosedTerm) -> (constraints : List Name) -> Def


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

-- Everything needed to typecheck data types/functions
export
record ContextDefs where
      constructor MkAllDefs
      gamma : Gamma -- All the definitions
      nextTag : Int -- next tag for type constructors
      nextHole : Int -- next hole/constraint id
      holes : List Name -- unsolved metavariables in gamma
      constraints : Context Constraint -- unsolved metavariable constraints 

initCtxt : ContextDefs
initCtxt = MkAllDefs empty 100 0 [] empty

export
lookupDef : Name -> Gamma -> Maybe Def
lookupDef n gam = do def <- lookupCtxt n gam
                     pure (definition def)

export
lookupDefTy : Name -> Gamma -> Maybe (Def, ClosedTerm)
lookupDefTy n gam = do def <- lookupCtxt n gam
                       pure (definition def, type def)

public export
record Constructor where
  constructor MkCon
  name : Name
  arity : Nat
  type : ClosedTerm

public export
data DataDef : Type where
     MkData : (tycon : Constructor) -> (datacons : List Constructor) ->
              DataDef

public export
data Clause : Type where
     MkClause : (env : Env Term vars) ->
                (lhs : Term vars) -> (rhs : Term vars) -> Clause

public export
data FnDef : Type where
     MkFn : (n : Name) -> (ty : ClosedTerm) -> (clauses : List Clause) ->
            FnDef

-- All possible errors
public export
data Error = CantConvert (Env Term vars) (Term vars) (Term vars)
           | UndefinedName Name
           | NotFunctionType (Term vars)
           | CaseCompile Name CaseError 
           | GenericMsg String

export
Show Error where
  show (CantConvert env x y) 
      = "Type mismatch: " ++ show x ++ " and " ++ show y
  show (UndefinedName x) = "Undefined name " ++ show x
  show (NotFunctionType tm) = "Not a function type: " ++ show tm
  show (CaseCompile n DifferingArgNumbers) 
       = "Patterns for " ++ show n ++ " have different numbers of arguments"
  show (GenericMsg str) = str

export
error : Error -> Either Error a
error = Left

-- When we're manipulating contexts, we can throw exceptions and log errors
-- TODO: Maybe ConsolIO should be a logging interface, therefore?
export
interface (Exception m Error, ConsoleIO m) =>
          CtxtManage (m : Type -> Type) where

export
(Exception m Error, ConsoleIO m) => CtxtManage m where

export
Defs : Type
Defs = State ContextDefs

export
getCtxt : (ctxt : Var) -> ST m Gamma [ctxt ::: Defs]
getCtxt ctxt = pure (gamma !(read ctxt))

export
getNextTypeTag : (ctxt : Var) -> ST m Int [ctxt ::: Defs]
getNextTypeTag ctxt 
    = do defs <- read ctxt
         let t = nextTag defs
         write ctxt (record { nextTag = t + 1 } defs)
         pure t

export
getNextHole : (ctxt : Var) -> ST m Int [ctxt ::: Defs]
getNextHole ctxt 
    = do defs <- read ctxt
         let t = nextHole defs
         write ctxt (record { nextHole = t + 1 } defs)
         pure t

export
setCtxt : (ctxt : Var) -> Gamma -> ST m () [ctxt ::: Defs]
setCtxt ctxt gam 
    = do st <- read ctxt
         write ctxt (record { gamma = gam } st)

export
newCtxt : ST m Var [add Defs]
newCtxt = new initCtxt

export
deleteCtxt : (ctxt : Var) -> ST m () [remove ctxt Defs]
deleteCtxt ctxt = delete ctxt

export
addDef : CtxtManage m => (ctxt : Var) -> Name -> GlobalDef -> 
                         ST m () [ctxt ::: Defs]
addDef ctxt n def 
    = do g <- getCtxt ctxt
         setCtxt ctxt (addCtxt n def g)

argToPat : ClosedTerm -> Pat
argToPat tm with (unapply tm)
  argToPat (apply (Ref (DataCon tag _) cn) args) | ArgsList 
         = PCon cn tag (assert_total (map argToPat args))
  argToPat (apply (Ref _ var) []) | ArgsList = PVar var
  argToPat (apply (PrimVal c) []) | ArgsList = PConst c
  argToPat (apply f args) | ArgsList = PAny

toPatClause : CtxtManage m =>
              (ctxt : Var) -> Name -> (ClosedTerm, ClosedTerm) ->
              ST m (List Pat, ClosedTerm) [ctxt ::: Defs]
toPatClause ctxt n (lhs, rhs) with (unapply lhs)
  toPatClause ctxt n (apply (Ref Func fn) args, rhs) | ArgsList 
      = case nameEq n fn of
             Nothing => throw (GenericMsg "Wrong function name in pattern LHS")
             Just Refl => do putStrLn $ "Clause: " ++ show (apply (Ref Func fn) args) ++ " = " ++ show rhs
                             pure (map argToPat args, rhs)
  toPatClause ctxt n (apply f args, rhs) | ArgsList 
      = throw (GenericMsg "Not a function name in pattern LHS")

-- Assumption (given 'ClosedTerm') is that the pattern variables are
-- explicitly named. We'll assign de Bruijn indices when we're done, and
-- the names of the top level variables we created are returned in 'args'
export
simpleCase : CtxtManage m =>
             (ctxt : Var) -> Name -> (def : CaseTree []) ->
             (clauses : List (ClosedTerm, ClosedTerm)) ->
             ST m (args ** CaseTree args) [ctxt ::: Defs]
simpleCase ctxt fn def clauses 
    = do ps <- mapST (toPatClause ctxt fn) clauses
         case patCompile ps def of
              Left err => throw (CaseCompile fn err)
              Right ok => pure ok

export
addFnDef : CtxtManage m =>
           (ctxt : Var) -> Visibility ->
           FnDef -> ST m () [ctxt ::: Defs]
addFnDef ctxt vis (MkFn n ty clauses) 
    = do let cs = map toClosed clauses
         (args ** tree) <- simpleCase ctxt n (Unmatched "Unmatched case") cs
         putStrLn $ "Case tree: " ++ show args ++ " " ++ show tree
         let def = MkGlobalDef ty vis (PMDef args tree)
         addDef ctxt n def
  where
    close : Int -> Env Term vars -> Term vars -> ClosedTerm
    close i [] tm = tm
    close i (b :: bs) tm 
        = close (i + 1) bs (subst (Ref Bound (MN "pat" i)) tm)

    toClosed : Clause -> (ClosedTerm, ClosedTerm)
    toClosed (MkClause env lhs rhs) 
          = (close 0 env lhs, close 0 env rhs)

export
addData : CtxtManage m =>
          (ctxt : Var) -> Visibility ->
          DataDef -> ST m () [ctxt ::: Defs]
addData ctxt vis (MkData (MkCon tyn arity tycon) datacons)
    = do gam <- getCtxt ctxt
         tag <- getNextTypeTag ctxt
         let tydef = MkGlobalDef tycon vis (TCon tag arity (map name datacons))
         let gam' = addCtxt tyn tydef gam
         setCtxt ctxt (addDataConstructors 0 datacons gam')
  where
    conVisibility : Visibility -> Visibility
    conVisibility Export = Private
    conVisibility x = x

    addDataConstructors : (tag : Int) -> 
                          List Constructor -> Gamma -> Gamma
    addDataConstructors tag [] gam = gam
    addDataConstructors tag (MkCon n a ty :: cs) gam
        = do let condef = MkGlobalDef ty (conVisibility vis) (DCon tag a)
             let gam' = addCtxt n condef gam
             addDataConstructors tag cs gam'

export
runWithCtxt : ST (IOExcept Error) () [] -> IO ()
runWithCtxt prog = ioe_run (run prog) 
                           (\err => printLn err)
                           (\ok => pure ())

--- Some test entries
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
