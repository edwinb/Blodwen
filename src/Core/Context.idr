module Core.Context

import Core.TT
import Core.CaseTree

import public Control.Monad.StateE
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
     PMDef : (ishole : Bool) -> (args : List Name) -> CaseTree args -> Def
     DCon  : (tag : Int) -> (arity : Nat) -> Def
     TCon  : (tag : Int) -> (arity : Nat) -> (datacons : List Name) -> Def

     Hole : (numlocs : Nat) -> Def -- Unsolved hole, under 'numlocs' locals
     ImpBind : Def -- Hole turned into an implicitly bound variable
                   -- (which will be deleted after elaboration)
     -- The constraint names refer into a context of constraints,
     -- defined in Core.Unify
     Guess : (guess : ClosedTerm) -> (constraints : List Name) -> Def

public export
data Visibility = Public | Export | Private

export
record GlobalDef where
     constructor MkGlobalDef
     type : ClosedTerm
     visibility : Visibility
     definition : Def

export
newDef : (ty : ClosedTerm) -> (vis : Visibility) -> Def -> GlobalDef
newDef ty vis def = MkGlobalDef ty vis def

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

initCtxt : ContextDefs
initCtxt = MkAllDefs empty 100 0

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
-- 'annot' is an annotation provided by the thing which called the
-- function which had an error; it's intended to provide any useful information
-- a high level language might need, e.g. file/line number
public export
data Error annot
    = CantConvert annot (Env Term vars) (Term vars) (Term vars)
    | Cycle annot (Env Term vars) (Term vars) (Term vars)
    | WhenUnifying annot (Term vars) (Term vars) (Error annot)
	  | UndefinedName annot Name
	  | NotFunctionType annot (Term vars)
	  | CaseCompile annot Name CaseError 
	  | GenericMsg annot String
    | InternalError String

export
Show (Error annot) where
  show (CantConvert _ env x y) 
      = "Type mismatch: " ++ show x ++ " and " ++ show y
  show (Cycle _ env x y) 
      = "Occurs check failed: " ++ show x ++ " and " ++ show y
  show (WhenUnifying _ x y err)
      = "When unifying: " ++ show x ++ " and " ++ show y ++ "\n\t" ++
        show err
  show (UndefinedName _ x) = "Undefined name " ++ show x
  show (NotFunctionType _ tm) = "Not a function type: " ++ show tm
  show (CaseCompile _ n DifferingArgNumbers) 
      = "Patterns for " ++ show n ++ " have different numbers of arguments"
  show (GenericMsg _ str) = str
  show (InternalError str) = "INTERNAL ERROR: " ++ str

export
error : Error annot -> Either (Error annot) a
error = Left

-- When we're manipulating contexts, we can throw exceptions and log errors
-- TODO: Maybe ConsoleIO should be a logging interface, therefore?
export
interface (Catchable m (Error annot), ConsoleIO m) =>
          CtxtManage (m : Type -> Type) annot | m where

export
(Catchable m (Error annot), ConsoleIO m) => CtxtManage m annot where

export
Defs : Type
Defs = ContextDefs

-- A label for the context in the global state
export
data Ctxt : Type where

public export
Core : Type -> StateInfo -> Type -> Type
Core annot s t 
    = {m : Type -> Type} -> (Monad m, CtxtManage m annot) => 
      SE s (Error annot) m t

public export
CoreI : Type -> (m : Type -> Type) -> StateInfo -> Type -> Type
CoreI annot m s t = ((Monad m, CtxtManage m annot) => SE s (Error annot) m t)

public export
CoreM : Type -> StateInfo -> StateInfo -> Type -> Type
CoreM annot s s' t 
    = {m : Type -> Type} -> 
	    (Monad m, CtxtManage m annot) => StatesE s s' (Error annot) m t

export
getCtxt : Core annot [Ctxt ::: Defs] Gamma
getCtxt = pure (gamma !(get Ctxt))

export
getNextTypeTag : Core annot [Ctxt ::: Defs] Int
getNextTypeTag 
    = do defs <- get Ctxt
         let t = nextTag defs
         put Ctxt (record { nextTag = t + 1 } defs)
         pure t

export
getNextHole : Core annot [Ctxt ::: Defs] Int
getNextHole 
    = do defs <- get Ctxt
         let t = nextHole defs
         put Ctxt (record { nextHole = t + 1 } defs)
         pure t

export
setCtxt : Gamma -> Core annot [Ctxt ::: Defs] ()
setCtxt gam 
    = do st <- get Ctxt
         put Ctxt (record { gamma = gam } st)

export
newCtxt : CoreM annot [] [Ctxt ::: Defs] ()
newCtxt = new Ctxt initCtxt

export
deleteCtxt : CoreM annot [Ctxt ::: Defs] [] ()
deleteCtxt = delete Ctxt

export
addDef : Name -> GlobalDef -> Core annot [Ctxt ::: Defs] ()
addDef n def 
    = do g <- getCtxt 
         setCtxt (addCtxt n def g)

export
updateDef : Name -> Def -> Core annot [Ctxt ::: Defs] ()
updateDef n def 
    = do g <- getCtxt
         case lookupCtxt n g of
              Nothing => throw (InternalError ("No such name to update " ++ show n))
              Just odef => 
                   let gdef = record { definition = def } odef in
                       setCtxt (addCtxt n gdef g)
 

argToPat : ClosedTerm -> Pat
argToPat tm with (unapply tm)
  argToPat (apply (Ref (DataCon tag _) cn) args) | ArgsList 
         = PCon cn tag (assert_total (map argToPat args))
  argToPat (apply (Ref _ var) []) | ArgsList = PVar var
  argToPat (apply (PrimVal c) []) | ArgsList = PConst c
  argToPat (apply f args) | ArgsList = PAny

toPatClause : annot -> Name -> (ClosedTerm, ClosedTerm) ->
              Core annot [Ctxt ::: Defs] (List Pat, ClosedTerm)
toPatClause loc n (lhs, rhs) with (unapply lhs)
  toPatClause loc n (apply (Ref Func fn) args, rhs) | ArgsList 
      = case nameEq n fn of
             Nothing => throw (GenericMsg loc "Wrong function name in pattern LHS")
             Just Refl => do -- putStrLn $ "Clause: " ++ show (apply (Ref Func fn) args) ++ " = " ++ show rhs
                             pure (map argToPat args, rhs)
  toPatClause loc n (apply f args, rhs) | ArgsList 
      = throw (GenericMsg loc "Not a function name in pattern LHS")

-- Assumption (given 'ClosedTerm') is that the pattern variables are
-- explicitly named. We'll assign de Bruijn indices when we're done, and
-- the names of the top level variables we created are returned in 'args'
export
simpleCase : annot -> Name -> (def : CaseTree []) ->
             (clauses : List (ClosedTerm, ClosedTerm)) ->
             Core annot [Ctxt ::: Defs] (args ** CaseTree args)
simpleCase loc fn def clauses 
      -- \x is needed below due to scoped implicits being weird...
    = do ps <- traverse (\x => toPatClause loc fn x) clauses
         case patCompile ps def of
              Left err => throw (CaseCompile loc fn err)
              Right ok => pure ok

export
addFnDef : annot -> Visibility ->
           FnDef -> Core annot [Ctxt ::: Defs] ()
addFnDef loc vis (MkFn n ty clauses) 
    = do let cs = map toClosed clauses
         (args ** tree) <- simpleCase loc n (Unmatched "Unmatched case") cs
         -- putStrLn $ "Case tree: " ++ show args ++ " " ++ show tree
         let def = newDef ty vis (PMDef False args tree)
         addDef n def
  where
    close : Int -> Env Term vars -> Term vars -> ClosedTerm
    close i [] tm = tm
    close i (b :: bs) tm 
        = close (i + 1) bs (subst (Ref Bound (MN "pat" i)) tm)

    toClosed : Clause -> (ClosedTerm, ClosedTerm)
    toClosed (MkClause env lhs rhs) 
          = (close 0 env lhs, close 0 env rhs)

export
addData : Visibility -> DataDef -> Core annot [Ctxt ::: Defs] ()
addData vis (MkData (MkCon tyn arity tycon) datacons)
    = do gam <- getCtxt 
         tag <- getNextTypeTag 
         let tydef = newDef tycon vis (TCon tag arity (map name datacons))
         let gam' = addCtxt tyn tydef gam
         setCtxt (addDataConstructors 0 datacons gam')
  where
    conVisibility : Visibility -> Visibility
    conVisibility Export = Private
    conVisibility x = x

    addDataConstructors : (tag : Int) -> 
                          List Constructor -> Gamma -> Gamma
    addDataConstructors tag [] gam = gam
    addDataConstructors tag (MkCon n a ty :: cs) gam
        = do let condef = newDef ty (conVisibility vis) (DCon tag a)
             let gam' = addCtxt n condef gam
             addDataConstructors tag cs gam'

export
runWithCtxt : Core annot [] () -> IO ()
runWithCtxt prog = ioe_run (runSTE prog []) 
                           (\err => printLn err)
                           (\ok => pure ())
