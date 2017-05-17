module Core.TT

import Data.List

%default total

%hide Raw -- from Reflection in the Prelude
%hide Binder
%hide NameType
%hide Case

public export
data Name = UN String
          | MN String Int
          | NS (List String) Name

public export
data NameType : Type where
     Func    : NameType
     DataCon : (tag : Int) -> (arity : Int) -> NameType
     TyCon   : (tag : Int) -> (arity : Int) -> NameType

export
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x y) (MN x' y') = x == x' && y == y'
  (==) (NS xs x) (NS xs' x') = xs == xs' && x == x'
  (==) _ _ = False

export
Ord Name where
  compare (UN _) (MN _ _) = LT
  compare (UN _) (NS _ _) = LT
  compare (MN _ _) (NS _ _) = LT

  compare (MN _ _) (UN _) = GT
  compare (NS _ _) (UN _) = GT
  compare (NS _ _) (MN _ _) = GT

  compare (UN x) (UN y) = compare x y
  compare (MN x y) (MN x' y') = case compare x x' of
                                     EQ => compare y y'
                                     t => t
  compare (NS x y) (NS x' y') = case compare x x' of
                                     EQ => compare y y'
                                     t => t

public export
data Constant = I Int
              | IntType

public export
data PiInfo = Implicit | Explicit | AutoImplicit | Constraint

public export
data Binder : Type -> Type where
     Lam : (ty : type) -> Binder type
     Let : (val : type) -> (ty : type) -> Binder type
     Pi : PiInfo -> (ty : type) -> Binder type

export
Functor Binder where
  map func (Lam ty) = Lam (func ty)
  map func (Let val ty) = Let (func val) (func ty)
  map func (Pi x ty) = Pi x (func ty)

namespace ArgList
  data ArgList : (tm : List Name -> Type) ->
                 List Name -> Type where
       Nil : ArgList tm []
       (::) : tm scope -> ArgList tm ns -> ArgList tm (n :: ns)

-- Typechecked terms
-- These are guaranteed to be well-scoped wrt local variables, because they are
-- indexed by the names of local variables in scope
public export
data Term : List Name -> Type where
     Local : Elem x scope -> Term scope
     Ref : NameType -> (fn : Name) -> Term scope
     Bind : (x : Name) -> Binder (Term scope) -> 
                          Term (x :: scope) -> Term scope
     App : Term scope -> Term scope -> Term scope
     PrimVal : Constant -> Term scope
     TType : Term scope

export
tm_id : Term []
tm_id = Bind (UN "ty") (Lam TType) $
        Bind (UN "x") (Lam (Local {x = UN "ty"} Here)) $
        Local {x = UN "x"} Here

%name TT.Binder b, b' 
%name TT.Term tm 

public export
ClosedTerm : Type
ClosedTerm = Term []

-- Environment containing types and values of local variables
namespace Env
  public export
  data Env : (tm : List Name -> Type) -> List Name -> Type where
       Nil : Env tm []
       (::) : Binder (tm scope) -> Env tm scope -> Env tm (x :: scope)

%name Env env

{- Some ugly mangling to allow us to extend the scope of a term - a
   term is always valid in a bigger scope than it needs. -}
insertElem : Elem x (outer ++ inner) -> Elem x (outer ++ n :: inner)
insertElem {outer = []} p = There p
insertElem {outer = (x :: xs)} Here = Here
insertElem {outer = (y :: xs)} (There later) 
   = There (insertElem {outer = xs} later)

thin : (n : Name) -> Term (outer ++ inner) -> Term (outer ++ n :: inner)
thin n (Local prf) = Local (insertElem prf)
thin n (Ref x fn) = Ref x fn
thin {outer} {inner} n (Bind x b sc) 
   = let sc' = thin {outer = x :: outer} {inner} n sc in
         assert_total $ Bind x (map (thin n) b) sc'
thin n (App f a) = App (thin n f) (thin n a)
thin n (PrimVal x) = PrimVal x
thin n TType = TType

public export
interface Weaken (tm : List Name -> Type) where
  weaken : tm scope -> tm (n :: scope)

export
Weaken Term where
  weaken tm = thin {outer = []} _ tm

export
weakenBinder : Weaken tm => Binder (tm scope) -> Binder (tm (n :: scope))
weakenBinder = map weaken

export
getBinder : Weaken tm => Elem x scope -> Env tm scope -> Binder (tm scope)
getBinder Here (b :: env) = map weaken b
getBinder (There later) (b :: env) = map weaken (getBinder later env)

-- Raw terms, not yet typechecked
public export
data Raw : Type where
     RVar : Name -> Raw
     RBind : Name -> Binder Raw -> Raw -> Raw
     RApp : Raw -> Raw -> Raw
     RPrimVal : Constant -> Raw
     RType : Raw


