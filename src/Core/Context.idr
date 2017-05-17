module Core.Context

import Core.TT
import Data.SortedMap

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

public export
data Def : Type where
     None : Def -- Not yet defined
     Fn : ClosedTerm -> Def
     DCon : (tag : Int) -> (arity : Int) -> Def
     TCon : (tag : Int) -> (arity : Int) -> Def

public export
record GlobalDef where
     constructor MkGlobalDef
     type : ClosedTerm
     definition : Def

-- A context of global definitions
public export
Gamma : Type
Gamma = Context GlobalDef

export
lookupDef : Name -> Gamma -> Maybe Def
lookupDef n gam = do def <- lookupCtxt n gam
                     pure (definition def)

