module Core.Context

import Core.TT
import Core.CaseTree
import public Core.Core

import public Control.Catchable

import Data.CMap
import Data.CSet
import Data.List

%default total

export
data Context : Type -> Type where
     MkContext : SortedMap a -> Context a

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

     Hole : (numlocs : Nat) -> (pvar : Bool) -> Def 
		           -- Unsolved hole, under 'numlocs' locals, and whether it
						   -- is standing for a pattern variable (and therefore mustn't
							 -- be solved)
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
     refersTo : List Name

getRefs : Def -> List Name
getRefs None = []
getRefs (PMDef ishole args sc) = getRefs sc
getRefs (DCon tag arity) = []
getRefs (TCon tag arity datacons) = []
getRefs (Hole numlocs _) = []
getRefs ImpBind = []
getRefs (Guess guess constraints) = CSet.toList (getRefs guess)

export
newDef : (ty : ClosedTerm) -> (vis : Visibility) -> Def -> GlobalDef
newDef ty vis def = MkGlobalDef ty vis def (getRefs def)

-- A context of global definitions
public export
Gamma : Type
Gamma = Context GlobalDef

-- Everything needed to typecheck data types/functions
export
record Defs where
      constructor MkAllDefs
      gamma : Gamma -- All the definitions
      nextTag : Int -- next tag for type constructors
      nextHole : Int -- next hole/constraint id
      nextVar	: Int

export
initCtxt : Defs
initCtxt = MkAllDefs empty 100 0 0

lookupGlobal : Name -> Gamma -> Maybe GlobalDef
lookupGlobal n gam = lookupCtxt n gam

export
lookupDef : Name -> Gamma -> Maybe Def
lookupDef n gam
    = do def <- lookupGlobal n gam
         pure (definition def)

export
lookupTy : Name -> Gamma -> Maybe ClosedTerm
lookupTy n gam 
    = do def <- lookupGlobal n gam
         pure (type def)

export
lookupDefTy : Name -> Gamma -> Maybe (Def, ClosedTerm)
lookupDefTy n gam 
    = do def <- lookupGlobal n gam
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


-- A label for the context in the global state
export
data Ctxt : Type where

export
getCtxt : {auto x : Ref Ctxt Defs} ->
					Core annot Gamma
getCtxt = pure (gamma !(get Ctxt))

export
getNextTypeTag : {auto x : Ref Ctxt Defs} ->
								 Core annot Int
getNextTypeTag
    = do defs <- get Ctxt
         let t = nextTag defs
         put Ctxt (record { nextTag = t + 1 } defs)
         pure t

export
getNextHole : {auto x : Ref Ctxt Defs} -> Core annot Int
getNextHole
    = do defs <- get Ctxt
         let t = nextHole defs
         put Ctxt (record { nextHole = t + 1 } defs)
         pure t

export
genName : {auto x : Ref Ctxt Defs} ->
					String -> Core annot Name
genName root
    = do ust <- get Ctxt
         put Ctxt (record { nextVar $= (+1) } ust)
         pure (MN root (nextVar ust))

export
setCtxt : {auto x : Ref Ctxt Defs} -> Gamma -> Core annot ()
setCtxt gam
    = do st <- get Ctxt
         put Ctxt (record { gamma = gam } st)

export
getDescendents : Name -> Gamma -> List Name
getDescendents n g
    = CSet.toList $ getAllDesc [n] empty g
  where
    getAllDesc : List Name -> SortedSet -> Gamma -> SortedSet
    getAllDesc [] ns g = ns
    getAllDesc (n :: rest) ns g
      = if contains n ns
           then getAllDesc rest ns g
           else case lookupGlobal n g of
                     Nothing => ns
                     Just def => assert_total $
											 let refs = refersTo def in
												 getAllDesc (rest ++ refs)
						                        (union ns (fromList refs)) g

export
addDef : {auto x : Ref Ctxt Defs} -> Name -> GlobalDef -> Core annot ()
addDef n def
    = do g <- getCtxt 
         setCtxt (addCtxt n def g)

export
updateDef : {auto x : Ref Ctxt Defs} ->
						Name -> Def -> Core annot ()
updateDef n def 
    = do g <- getCtxt
         case lookupCtxt n g of
              Nothing => throw (InternalError ("No such name to update " ++ show n))
              Just odef => 
                   let gdef = record { definition = def,
																		   refersTo = getRefs def } odef in
                       setCtxt (addCtxt n gdef g)
 

argToPat : ClosedTerm -> Pat
argToPat tm with (unapply tm)
  argToPat (apply (Ref (DataCon tag _) cn) args) | ArgsList 
         = PCon cn tag (assert_total (map argToPat args))
  argToPat (apply (Ref _ var) []) | ArgsList = PVar var
  argToPat (apply (PrimVal c) []) | ArgsList = PConst c
  argToPat (apply f args) | ArgsList = PAny

toPatClause : {auto x : Ref Ctxt Defs} ->
							annot -> Name -> (ClosedTerm, ClosedTerm) ->
              Core annot (List Pat, ClosedTerm)
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
simpleCase : {auto x : Ref Ctxt Defs} ->
						 annot -> Name -> (def : CaseTree []) ->
             (clauses : List (ClosedTerm, ClosedTerm)) ->
             Core annot (args ** CaseTree args)
simpleCase loc fn def clauses 
      -- \x is needed below due to scoped implicits being weird...
    = do ps <- traverse (\x => toPatClause loc fn x) clauses
         case patCompile ps def of
              Left err => throw (CaseCompile loc fn err)
              Right ok => pure ok

export
addFnDef : {auto x : Ref Ctxt Defs} ->
					 annot -> Visibility ->
           FnDef -> Core annot ()
addFnDef loc vis (MkFn n ty clauses) 
    = do let cs = map toClosed clauses
         (args ** tree) <- simpleCase loc n (Unmatched "Unmatched case") cs
--          log 5 $ "Case tree for " ++ show n ++ ": " 
-- 				             ++ show args ++ "\n" ++ show cs ++ "\n" ++ show tree
         let def = newDef ty vis (PMDef False args tree)
         addDef n def
  where
    close : Int -> (plets : Bool) -> Env Term vars -> Term vars -> ClosedTerm
    close i plets [] tm = tm
    close i True (PLet val ty :: bs) tm 
		    = close (i + 1) True bs (Bind (MN "pat" i) (Let val ty) (renameTop _ tm))
    close i plets (b :: bs) tm 
        = close (i + 1) plets bs (subst (Ref Bound (MN "pat" i)) tm)

    toClosed : Clause -> (ClosedTerm, ClosedTerm)
    toClosed (MkClause env lhs rhs) 
          = (close 0 False env lhs, close 0 True env rhs)

export
addData : {auto x : Ref Ctxt Defs} ->
					Visibility -> DataDef -> Core annot ()
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
             addDataConstructors (tag + 1) cs gam'

export
runWithCtxt : Core annot () -> IO ()
runWithCtxt prog = coreRun prog 
                           (\err => printLn err)
                           (\ok => pure ())
