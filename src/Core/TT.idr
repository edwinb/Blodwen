module Core.TT

import Data.List
import Data.CSet
import Language.Reflection

import public Core.Name

%default total

%hide Raw -- from Reflection in the Prelude
%hide Binder
%hide NameType
%hide Case

public export
data NameType : Type where
     Bound   : NameType
     Func    : NameType
     DataCon : (tag : Int) -> (arity : Nat) -> NameType
     TyCon   : (tag : Int) -> (arity : Nat) -> NameType

%name TT.NameType nt

public export
data Constant 
	  = I Int
    | BI Integer
    | Str String
    | Ch Char
    | Db Double
    | WorldVal

    | IntType
		| IntegerType
    | StringType
    | CharType
    | DoubleType
    | WorldType

export
constantEq : (x, y : Constant) -> Maybe (x = y)
constantEq (I x) (I y) = case decEq x y of
                              Yes Refl => Just Refl
                              No contra => Nothing
constantEq (BI x) (BI y) = case decEq x y of
                                Yes Refl => Just Refl
                                No contra => Nothing
constantEq (Str x) (Str y) = case decEq x y of
                                  Yes Refl => Just Refl
                                  No contra => Nothing
constantEq (Ch x) (Ch y) = case decEq x y of
                                Yes Refl => Just Refl
                                No contra => Nothing
constantEq (Db x) (Db y) = Nothing -- no DecEq for Doubles!
constantEq WorldVal WorldVal = Just Refl
constantEq IntType IntType = Just Refl
constantEq IntegerType IntegerType = Just Refl
constantEq StringType StringType = Just Refl
constantEq CharType CharType = Just Refl
constantEq DoubleType DoubleType = Just Refl
constantEq WorldType WorldType = Just Refl
constantEq _ _ = Nothing

export
Show Constant where
  show (I x) = show x
  show (BI x) = show x
  show (Str x) = show x
  show (Ch x) = show x
  show (Db x) = show x
  show WorldVal = "%MkWorld"
  show IntType = "Int"
  show IntegerType = "Integer"
  show StringType = "String"
  show CharType = "Char"
  show DoubleType = "Double"
  show WorldType = "%World"

export
Eq Constant where
  (I x) == (I y) = x == y
  (BI x) == (BI y) = x == y
  (Str x) == (Str y) = x == y
  (Ch x) == (Ch y) = x == y
  (Db x) == (Db y) = x == y
  WorldVal == WorldVal = True
  IntType == IntType = True
  IntegerType == IntegerType = True
  StringType == StringType = True
  CharType == CharType = True
  DoubleType == DoubleType = True
  WorldType == WorldType = True
  _ == _ = False

-- All the internal operators, parameterised by their arity
public export
data PrimFn : Nat -> Type where
     Add : (ty : Constant) -> PrimFn 2
     Sub : (ty : Constant) -> PrimFn 2
     Mul : (ty : Constant) -> PrimFn 2
     Div : (ty : Constant) -> PrimFn 2
     Mod : (ty : Constant) -> PrimFn 2
     Neg : (ty : Constant) -> PrimFn 1

     LT  : (ty : Constant) -> PrimFn 2
     LTE : (ty : Constant) -> PrimFn 2
     EQ  : (ty : Constant) -> PrimFn 2
     GTE : (ty : Constant) -> PrimFn 2
     GT  : (ty : Constant) -> PrimFn 2

     StrLength : PrimFn 1
     StrHead : PrimFn 1
     StrTail : PrimFn 1
     StrAppend : PrimFn 2
     StrReverse : PrimFn 1

     Cast : Constant -> Constant -> PrimFn 1

public export
data PiInfo = Implicit | Explicit | AutoImplicit

export
Eq PiInfo where
  (==) Implicit Implicit = True
  (==) Explicit Explicit = True
  (==) AutoImplicit AutoImplicit = True
  (==) _ _ = False

-- Multiplicities on binders, for checking linear and erased types
-- TODO: This doesn't actually do anything yet, but I wanted to add it to
-- the representation early so that there's less to change in the data types
-- Needs updates in: Core.Typecheck and TTImp.Elab.Term, at least, and
-- dealing with how to bind pattern names in TTImp.Elab.State

-- Also need updating RawImp and PTerm syntax
public export
data RigCount = Rig0 | Rig1 | RigW

export
Eq RigCount where
  (==) Rig0 Rig0 = True
  (==) Rig1 Rig1 = True
  (==) RigW RigW = True
  (==) _ _ = False

export
Ord RigCount where
  compare Rig0 Rig0 = EQ
  compare Rig0 Rig1 = LT
  compare Rig0 RigW = LT

  compare Rig1 Rig0 = GT
  compare Rig1 Rig1 = EQ
  compare Rig1 RigW = LT

  compare RigW Rig0 = GT
  compare RigW Rig1 = GT
  compare RigW RigW = EQ

export
Show RigCount where
  show Rig0 = "Rig0"
  show Rig1 = "Rig1"
  show RigW = "RigW"

export
rigPlus : RigCount -> RigCount -> RigCount
rigPlus Rig0 Rig0 = Rig0
rigPlus Rig0 Rig1 = Rig1
rigPlus Rig0 RigW = RigW
rigPlus Rig1 Rig0 = Rig1
rigPlus Rig1 Rig1 = RigW
rigPlus Rig1 RigW = RigW
rigPlus RigW Rig0 = RigW
rigPlus RigW Rig1 = RigW
rigPlus RigW RigW = RigW

export
rigMult : RigCount -> RigCount -> RigCount
rigMult Rig0 Rig0 = Rig0
rigMult Rig0 Rig1 = Rig0
rigMult Rig0 RigW = Rig0
rigMult Rig1 Rig0 = Rig0
rigMult Rig1 Rig1 = Rig1
rigMult Rig1 RigW = RigW
rigMult RigW Rig0 = Rig0
rigMult RigW Rig1 = RigW
rigMult RigW RigW = RigW

public export
data Binder : Type -> Type where
	   -- Lambda bound variables with their implicitness
     Lam : RigCount -> PiInfo -> (ty : type) -> Binder type
		 -- Let bound variables with their value
     Let : RigCount -> (val : type) -> (ty : type) -> Binder type
		 -- Forall/pi bound variables with their implicitness
     Pi : RigCount -> PiInfo -> (ty : type) -> Binder type
		 -- pattern bound variables
     PVar : RigCount -> (ty : type) -> Binder type 
		 -- pattern bound variables with a known value (e.g. @ patterns or
		 -- variables unified with something else)
	   -- Like 'Let' but no computational force
     PLet : RigCount -> (val : type) -> (ty : type) -> Binder type 
		 -- the type of pattern bound variables
     PVTy : RigCount -> (ty : type) -> Binder type

export
binderType : Binder tm -> tm
binderType (Lam _ x ty) = ty
binderType (Let _ val ty) = ty
binderType (Pi _ x ty) = ty
binderType (PVar _ ty) = ty
binderType (PLet _ val ty) = ty
binderType (PVTy _ ty) = ty
  
export
multiplicity : Binder tm -> RigCount
multiplicity (Lam c x ty) = c
multiplicity (Let c val ty) = c
multiplicity (Pi c x ty) = c
multiplicity (PVar c ty) = c
multiplicity (PLet c val ty) = c
multiplicity (PVTy c ty) = c
  
export
setMultiplicity : Binder tm -> RigCount -> Binder tm
setMultiplicity (Lam c x ty) c' = Lam c' x ty
setMultiplicity (Let c val ty) c' = Let c' val ty
setMultiplicity (Pi c x ty) c' = Pi c' x ty
setMultiplicity (PVar c ty) c' = PVar c' ty
setMultiplicity (PLet c val ty) c' = PLet c' val ty
setMultiplicity (PVTy c ty) c' = PVTy c' ty
  
Show ty => Show (Binder ty) where
	show (Lam _ _ t) = "\\" ++ show t
	show (Pi _ _ t) = "Pi " ++ show t
	show (Let _ v t) = "let " ++ show v ++ " : " ++ show t
	show (PVar _ t) = "pat " ++ show t
	show (PLet _ v t) = "plet " ++ show v ++ ": " ++ show t
	show (PVTy _ t) = "pty " ++ show t

export
setType : Binder tm -> tm -> Binder tm
setType (Lam c x _) ty = Lam c x ty
setType (Let c val _) ty = Let c val ty
setType (Pi c x _) ty = Pi c x ty
setType (PVar c _) ty = PVar c ty
setType (PLet c val _) ty = PLet c val ty
setType (PVTy c _) ty = PVTy c ty

export
Functor Binder where
  map func (Lam c x ty) = Lam c x (func ty)
  map func (Let c val ty) = Let c (func val) (func ty)
  map func (Pi c x ty) = Pi c x (func ty)
  map func (PVar c ty) = PVar c (func ty)
  map func (PLet c val ty) = PLet c (func val) (func ty)
  map func (PVTy c ty) = PVTy c (func ty)

-- Typechecked terms
-- These are guaranteed to be well-scoped wrt local variables, because they are
-- indexed by the names of local variables in scope
public export
data Term : List Name -> Type where
     Local : Elem x vars -> Term vars
     Ref : NameType -> (fn : Name) -> Term vars
     Bind : (x : Name) -> Binder (Term vars) -> 
                          Term (x :: vars) -> Term vars
     App : Term vars -> Term vars -> Term vars
     PrimVal : Constant -> Term vars
     Erased : Term vars
     TType : Term vars

public export
data Visibility = Private | Export | Public

export
Show Visibility where
  show Private = "private"
  show Export = "export"
  show Public = "public export"

export
Eq Visibility where
  Private == Private = True
  Export == Export = True
  Public == Public = True
  _ == _ = False

export
Ord Visibility where
  compare Private Export = LT
  compare Private Public = LT
  compare Export Public = LT

  compare Private Private = EQ
  compare Export Export = EQ
  compare Public Public = EQ

  compare Export Private = GT
  compare Public Private = GT
  compare Public Export = GT

public export
data PartialReason = NotCovering | NotStrictlyPositive 
                   | Calling (List Name)

public export
data Totality = Partial PartialReason | Unchecked | Covering | Total 

data SameElem : Elem x xs -> Elem x' xs -> Type where
     SameHere : SameElem Here Here
     SameThere : SameElem p1 p2 -> SameElem (There p1) (There p2)

hereNotThere : SameElem Here (There later) -> Void
hereNotThere SameHere impossible
hereNotThere (SameThere _) impossible

thereNotHere : SameElem (There later) Here -> Void
thereNotHere SameHere impossible
thereNotHere (SameThere _) impossible

thereLater : (same : SameElem p1 p2 -> Void) -> SameElem (There p1) (There p2) -> Void
thereLater same (SameThere p) = same p

sameElem : (p1 : Elem x xs) -> (p2 : Elem x' xs) -> Dec (SameElem p1 p2)
sameElem Here Here = Yes SameHere
sameElem Here (There later) = No hereNotThere
sameElem (There later) Here = No thereNotHere
sameElem (There p1) (There p2) with (sameElem p1 p2)
  sameElem (There p1) (There p2) | No same = No (thereLater same)
  sameElem (There p1) (There p2) | (Yes later) = Yes (SameThere later)

export
sameVar : Elem x xs -> Elem y xs -> Bool
sameVar p1 p2 = case sameElem p1 p2 of
                     Yes prf => True
                     No contra => False

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
       (::) : Binder (tm vars) -> Env tm vars -> Env tm (x :: vars)

  export
  extend : (x : Name) -> Binder (tm vars) -> Env tm vars -> Env tm (x :: vars)
  extend x = (::) {x} 

  export
  length : Env tm xs -> Nat
  length [] = 0
  length (x :: xs) = S (length xs)

-- Also define Values here - NF represents a term in head normal form.
-- That is - the top level constructor is known but the arguments aren't
-- evaluted. Terms are evaluated to NF in Core.Normalise.

-- Closures are terms linked with the environment they evaluate in.
-- That's a local environment - local variables in the evaluation itself -
-- and an environment describing the free variables
mutual
  public export
  data LocalEnv : List Name -> List Name -> Type where
       Nil  : LocalEnv free []
       (::) : Closure free -> LocalEnv free vars -> LocalEnv free (x :: vars)

  public export
  data Closure : List Name -> Type where
       MkClosure : (holesonly : Bool) ->
                   LocalEnv free vars -> 
                   Env Term free ->
                   Term (vars ++ free) -> Closure free

-- The head of a value: things you can apply arguments to
public export
data NHead : List Name -> Type where
     NLocal : Elem x vars -> NHead vars
     NRef   : NameType -> Name -> NHead vars

-- Values themselves
public export
data NF : List Name -> Type where
     NBind    : (x : Name) -> Binder (NF vars) ->
                (Closure vars -> NF vars) -> NF vars
     NApp     : NHead vars -> List (Closure vars) -> NF vars
     NDCon    : Name -> (tag : Int) -> (arity : Nat) -> 
                List (Closure vars) -> NF vars
     NTCon    : Name -> (tag : Int) -> (arity : Nat) -> 
                List (Closure vars) -> NF vars
     NPrimVal : Constant -> NF vars
     NErased  : NF vars
     NType    : NF vars

%name Env env

namespace AList
  public export
	data AList : Type -> List b -> Type where
       Nil : AList a []
       (::) : (val : a) -> AList a xs -> AList a (x :: xs) -- 'val' corresponds to x

  export
  getCorresponding : (as : AList ty xs) -> Elem x xs -> ty
  getCorresponding (val :: _) Here = val
  getCorresponding (val :: as) (There later) = getCorresponding as later

%name AList as

export
defined : (n : Name) -> Env Term vars -> Maybe (RigCount, Elem n vars)
defined n [] = Nothing
defined {vars = x :: xs} n (b :: env) with (nameEq x n)
  defined {vars = n :: xs} n (b :: env) | (Just Refl) 
      = Just (multiplicity b, Here)
  defined {vars = x :: xs} n (b :: env) | Nothing 
      = do (m, el) <- defined n env
           Just (m, There el)

{- Some ugly mangling to allow us to extend the scope of a term - a
   term is always valid in a bigger scope than it needs. -}
insertElem : Elem x (outer ++ inner) -> Elem x (outer ++ n :: inner)
insertElem {outer = []} p = There p
insertElem {outer = (x :: xs)} Here = Here
insertElem {outer = (y :: xs)} (There later) 
   = There (insertElem {outer = xs} later)

export
thin : (n : Name) -> Term (outer ++ inner) -> Term (outer ++ n :: inner)
thin n (Local prf) = Local (insertElem prf)
thin n (Ref x fn) = Ref x fn
thin {outer} {inner} n (Bind x b sc) 
   = let sc' = thin {outer = x :: outer} {inner} n sc in
         Bind x (assert_total (map (thin n) b)) sc'
thin n (App f a) = App (thin n f) (thin n a)
thin n (PrimVal x) = PrimVal x
thin n Erased = Erased
thin n TType = TType

export
weakenElem : Elem x xs -> Elem x (ns ++ xs)
weakenElem {ns = []} p = p
weakenElem {ns = (x :: xs)} p = There (weakenElem p)

export
insertElemNames : (ns : List Name) -> Elem x (outer ++ inner) ->
                  Elem x (outer ++ (ns ++ inner))
insertElemNames {outer = []} ns p = weakenElem p
insertElemNames {outer = (x :: xs)} ns Here = Here
insertElemNames {outer = (x :: xs)} ns (There later) 
    = There (insertElemNames ns later)

export
insertNames : (ns : List Name) -> Term (outer ++ inner) ->
              Term (outer ++ (ns ++ inner))
insertNames ns (Local prf) = Local (insertElemNames ns prf)
insertNames ns (Ref x fn) = Ref x fn
insertNames {outer} {inner} ns (Bind x b sc) 
    = Bind x (assert_total (map (insertNames ns) b)) 
             (insertNames {outer = x :: outer} {inner} ns sc)
insertNames ns (App fn arg) = App (insertNames ns fn) (insertNames ns arg)
insertNames ns (PrimVal x) = PrimVal x
insertNames ns Erased = Erased
insertNames ns TType = TType

export
elemExtend : Elem x xs -> Elem x (xs ++ ys)
elemExtend Here = Here
elemExtend (There later) = There (elemExtend later)

export
embed : Term vars -> Term (vars ++ more)
embed (Local prf) = Local (elemExtend prf)
embed (Ref x fn) = Ref x fn
embed (Bind x b tm) = Bind x (assert_total (map embed b)) (embed tm)
embed (App f a) = App (embed f) (embed a)
embed (PrimVal x) = PrimVal x
embed Erased = Erased
embed TType = TType

public export
interface Weaken (tm : List Name -> Type) where
  weaken : tm vars -> tm (n :: vars)
  weakenNs : (ns : List Name) -> tm vars -> tm (ns ++ vars)

  weakenNs [] t = t
  weakenNs (n :: ns) t = weaken (weakenNs ns t)

  weaken = weakenNs [_]

export
Weaken Term where
  weaken tm = thin {outer = []} _ tm
  weakenNs ns tm = insertNames {outer = []} ns tm

export
weakenBinder : Weaken tm => Binder (tm vars) -> Binder (tm (n :: vars))
weakenBinder = map weaken

export
getBinder : Weaken tm => Elem x vars -> Env tm vars -> Binder (tm vars)
getBinder Here (b :: env) = map weaken b
getBinder (There later) (b :: env) = map weaken (getBinder later env)

-- Some syntax manipulation

export
addVar : Elem var (later ++ vars) -> Elem var (later ++ x :: vars)
addVar {later = []} prf = There prf
addVar {later = (var :: xs)} Here = Here
addVar {later = (y :: xs)} (There prf) = There (addVar prf)

export
localPrf : Elem fn (later ++ fn :: vars)
localPrf {later = []} = Here
localPrf {later = (x :: xs)} = There localPrf

export
mkLocal : (x : Name) -> 
          Elem new (later ++ new :: vars) ->
          Term (later ++ vars) -> Term (later ++ new :: vars)
mkLocal x loc (Local prf) = Local (addVar prf)
mkLocal x loc (Ref y fn) with (x == fn)
  mkLocal x loc (Ref y fn) | True = Local loc
  mkLocal x loc (Ref y fn) | False = Ref y fn
mkLocal {later} x loc (Bind y b tm) 
    = Bind y (assert_total (map (mkLocal x loc) b)) 
             (mkLocal {later = y :: later} x (There loc) tm)
mkLocal x loc (App f a) = App (mkLocal x loc f) (mkLocal x loc a)
mkLocal x loc (PrimVal y) = PrimVal y
mkLocal x loc Erased = Erased
mkLocal x loc TType = TType

-- Replace any reference to 'x' with a locally bound name 'new'
export
refToLocal : (x : Name) -> (new : Name) -> Term vars -> Term (new :: vars)
refToLocal x new tm = mkLocal {later = []} x Here tm

export
refToLocals : (ns : List Name) -> Term vars -> Term (ns ++ vars)
refToLocals [] tm = tm
refToLocals (n :: ns) tm = refToLocal n n (refToLocals ns tm)

-- Oops, no DecEq for Name, so we need this
export
isVar : (n : Name) -> (ns : List Name) -> Maybe (Elem n ns)
isVar n [] = Nothing
isVar n (m :: ms) 
    = case nameEq n m of
           Nothing => do p <- isVar n ms
                         pure (There p)
           Just Refl => pure Here

-- Replace any Ref Bound with appropriate proof
export
resolveRefs : (vars : List Name) -> Term vars -> Term vars
resolveRefs vars (Ref Bound n)
    = case isVar n vars of
           Just prf => Local prf
           _ => Ref Bound n
resolveRefs vars (Bind x b sc)
    = Bind x (assert_total (map (resolveRefs vars) b))
             (resolveRefs (x :: vars) sc)
resolveRefs vars (App f a) = App (resolveRefs vars f) (resolveRefs vars a)
resolveRefs vars tm = tm

export
innerRefToLocals : (ns : List Name) -> 
                   Term (outer ++ vars) -> Term (outer ++ ns ++ vars)
innerRefToLocals [] tm = tm
innerRefToLocals (n :: ns) tm 
     = mkLocal n {new = n} localPrf (innerRefToLocals ns tm)

-- Substitute some explicit terms for names in a term, and remove those
-- names from the scope
namespace SubstEnv
  data SubstEnv : List Name -> List Name -> Type where
       Nil : SubstEnv [] vars
       (::) : Term vars -> 
              SubstEnv ds vars -> SubstEnv (d :: ds) vars

  findDrop : Elem x (drop ++ vars) -> SubstEnv drop vars -> Term vars
  findDrop {drop = []} var env = Local var
  findDrop {drop = (x :: xs)} Here (tm :: env) = tm
  findDrop {drop = (x :: xs)} (There later) (tm :: env) = findDrop later env

  find : Elem x (outer ++ (drop ++ vars)) ->
         SubstEnv drop vars ->
         Term (outer ++ vars)
  find {outer = []} var env = findDrop var env
  find {outer = (x :: xs)} Here env = Local Here
  find {outer = (x :: xs)} (There later) env = weaken (find later env)

  substEnv : SubstEnv drop vars -> Term (outer ++ (drop ++ vars)) -> 
             Term (outer ++ vars)
  substEnv env (Local prf) = find prf env
  substEnv env (Ref y fn) = Ref y fn
  substEnv {outer} env (Bind y b tm) 
      = Bind y (assert_total (map (substEnv env) b)) 
               (substEnv {outer = y :: outer} env tm)
  substEnv env (App fn arg) = App (substEnv env fn) (substEnv env arg)
  substEnv env (PrimVal y) = PrimVal y
  substEnv env Erased = Erased
  substEnv env TType = TType
      
-- Replace the most recently bound name with a term
export
subst : Term vars -> Term (x :: vars) -> Term vars
subst val tm = substEnv {outer = []} {drop = [_]} [val] tm

-- Replace an explicit name with a term
export
substName : Name -> Term vars -> Term vars -> Term vars
substName x new (Local p) = Local p
substName x new (Ref nt fn) 
    = case nameEq x fn of
           Nothing => Ref nt fn
           Just Refl => new
-- ASSUMPTION: When we substitute under binders, the name has always been
-- resolved to a Local, so no need to check that x isn't shadowing
substName x new (Bind y b tm) 
    = Bind y (assert_total (map (substName x new) b)) 
             (substName x (weaken new) tm)
substName x new (App fn arg) = App (substName x new fn) (substName x new arg)
substName x new (PrimVal y) = PrimVal y
substName x new Erased = Erased
substName x new TType = TType

-- Make a type which abstracts over an environment
-- Don't include 'let' bindings, since they have a concrete value and
-- shouldn't be generalised
export
abstractEnvType : Env Term vars -> (tm : Term vars) -> ClosedTerm
abstractEnvType [] tm = tm
abstractEnvType (Let c val ty :: env) tm
    = abstractEnvType env (subst val tm)
abstractEnvType (b :: env) tm 
    = abstractEnvType env (Bind _ 
						(Pi (multiplicity b) Explicit (binderType b)) tm)

export
abstractFullEnvType : Env Term vars -> (tm : Term vars) -> ClosedTerm
abstractFullEnvType [] tm = tm
abstractFullEnvType (b :: env) tm 
    = abstractFullEnvType env (Bind _ 
						(Pi (multiplicity b) Explicit (binderType b)) tm)

export
letToLam : Env Term vars -> Env Term vars
letToLam [] = []
letToLam (Let c val ty :: env) = Lam c Explicit ty :: letToLam env
letToLam (b :: env) = b :: letToLam env

public export
data SubVars : List Name -> List Name -> Type where
     SubRefl  : SubVars xs xs
     DropCons : SubVars xs ys -> SubVars xs (y :: ys)
     KeepCons : SubVars xs ys -> SubVars (x :: xs) (x :: ys)

subElem : Elem x xs -> SubVars ys xs -> Maybe (Elem x ys)
subElem prf SubRefl = Just prf
subElem Here (DropCons ds) = Nothing
subElem (There later) (DropCons ds) 
       = Just !(subElem later ds)
subElem Here (KeepCons ds) = Just Here
subElem (There later) (KeepCons ds) 
       = Just (There !(subElem later ds))

changeVar : (old : Elem x vs) -> (new : Elem x vs) -> Term vs -> Term vs
changeVar old new (Local y) 
    = if sameVar old y
         then Local new
         else Local y
changeVar old new (Bind x b sc) 
    = Bind x (assert_total (map (changeVar old new) b)) 
		         (changeVar (There old) (There new) sc)
changeVar old new (App fn arg) 
    = App (changeVar old new fn) (changeVar old new arg)
changeVar old new tm = tm

findLater : (newer : List Name) -> Elem x (newer ++ x :: older)
findLater [] = Here
findLater (x :: xs) = There (findLater xs)

-- For any variable in vs', re-abstract over it in the term
export
absSmaller : Env Term vs -> SubVars vs' vs -> 
						 Term (done ++ vs) -> Term (done ++ vs)
absSmaller [] SubRefl tm = tm
absSmaller {done} {vs = x :: vars} (b :: env) SubRefl tm 
     -- need to rebind 'b' in tm with a new name. So, weaken 'tm' then 
		 -- replace 'There Here' with 'Here'.
	 = let bindervs : Binder (Term (done ++ (x :: vars)))
	                    = rewrite appendAssociative done [x] vars in
															  map (weakenNs (done ++ [x])) b
	       btm = Bind x (Pi (multiplicity b) Explicit (binderType bindervs)) 
				            (changeVar (findLater (x :: done)) Here (weaken tm)) in
         rewrite appendAssociative done [x] vars in
				         absSmaller {done = done ++ [x]} env SubRefl 
                      (rewrite sym (appendAssociative done [x] vars) in btm)
absSmaller {done} {vs = x :: vars} (b :: env) (DropCons sub) tm 
  = rewrite appendAssociative done [x] vars in
            absSmaller {done = done ++ [x]} env sub
               (rewrite sym (appendAssociative done [x] vars) in tm)
absSmaller {done} {vs = x :: vars} (b :: env) (KeepCons sub) tm
  = let bindervs : Binder (Term (done ++ (x :: vars)))
                      = rewrite appendAssociative done [x] vars in
                                map (weakenNs (done ++ [x])) b
        btm = Bind x (Pi (multiplicity b) Explicit (binderType bindervs)) 
                   (changeVar (findLater (x :: done)) Here (weaken tm)) in
        rewrite appendAssociative done [x] vars in
                absSmaller {done = done ++ [x]} env sub
                    (rewrite sym (appendAssociative done [x] vars) in btm)



-- Would be handy if binders were Traversable...

mutual
  shrinkBinder : Binder (Term vars) -> SubVars newvars vars -> 
                 Maybe (Binder (Term newvars))
  shrinkBinder (Lam c x ty) subprf 
      = Just (Lam c x !(shrinkTerm ty subprf))
  shrinkBinder (Let c val ty) subprf 
      = Just (Let c !(shrinkTerm val subprf)
                    !(shrinkTerm ty subprf))
  shrinkBinder (Pi c x ty) subprf 
      = Just (Pi c x !(shrinkTerm ty subprf))
  shrinkBinder (PVar c ty) subprf 
      = Just (PVar c !(shrinkTerm ty subprf))
  shrinkBinder (PLet c val ty) subprf 
      = Just (PLet c !(shrinkTerm val subprf)
                     !(shrinkTerm ty subprf))
  shrinkBinder (PVTy c ty) subprf 
      = Just (PVTy c !(shrinkTerm ty subprf))

  -- Try to make a term which uses fewer variables, as long as it only uses
  -- the variables given as a subset
  export
  shrinkTerm : Term vars -> SubVars newvars vars -> Maybe (Term newvars)
  shrinkTerm (Local y) subprf = Just (Local !(subElem y subprf))
  shrinkTerm (Ref nt fn) subprf = Just (Ref nt fn)
  shrinkTerm (Bind x b sc) subprf 
      = do sc' <- shrinkTerm sc (KeepCons subprf)
           b' <- shrinkBinder b subprf
           Just (Bind x b' sc')
  shrinkTerm (App fn arg) subprf 
      = Just (App !(shrinkTerm fn subprf) !(shrinkTerm arg subprf))
  shrinkTerm (PrimVal x) subprf = Just (PrimVal x)
  shrinkTerm Erased subprf = Just Erased
  shrinkTerm TType subprf = Just TType
      
export
shrinkEnv : Env Term vars -> SubVars newvars vars -> Maybe (Env Term newvars)
shrinkEnv env SubRefl = Just env
shrinkEnv (b :: env) (DropCons p) = shrinkEnv env p
shrinkEnv (b :: env) (KeepCons p) 
    = do env' <- shrinkEnv env p
         b' <- shrinkBinder b p
         pure (b' :: env')

isUsed : Elem x vars -> List (y ** Elem y vars) -> Bool
isUsed el [] = False
isUsed el ((_ ** el') :: els) = sameVar el el' || isUsed el els

dropHere : List (x ** Elem x (n :: xs)) -> List (x ** Elem x xs)
dropHere [] = []
dropHere ((_ ** Here) :: xs) = dropHere xs
dropHere ((_ ** There p) :: xs) = (_ ** p) :: dropHere xs

-- This is kind of ugly - we're building a proof that some variables are
-- a subset of the larger set of variables, if those variables are in the
-- list of membership proofs.
-- We'll then use this to shrink the environment needed for a term using
-- 'shrinkEnv' above.
-- The ugliness is that 'shrinkEnv' returns a Maybe and if we get the first
-- step right, shrinking should always succeed!
-- It would be nice to prove this step, but in the absence of such a proof
-- we'll just build the SubVars structure and return the original environment
-- if shrinking fails for the moment.
mkShrinkSub : (vars : _) -> List (x ** Elem x (n :: vars)) -> 
              (newvars ** SubVars newvars (n :: vars))
mkShrinkSub [] els 
    = if isUsed Here els
         then (_ ** KeepCons SubRefl)
         else (_ ** DropCons SubRefl)
mkShrinkSub (x :: xs) els 
    = let (_ ** subRest) = mkShrinkSub xs (dropHere els) in
					if isUsed Here els
				     then (_ ** KeepCons subRest)
				     else (_ ** DropCons subRest)

mkShrink : List (x ** Elem x vars) -> 
           (newvars ** SubVars newvars vars)
mkShrink {vars = []} xs = (_ ** SubRefl)
mkShrink {vars = v :: vs} xs = mkShrinkSub _ xs

mutual
  findUsedLocs : Env Term vars -> Term vars -> List (x ** Elem x vars)
  findUsedLocs env (Local y) 
	  = (_ ** y) :: assert_total (findUsedInBinder env (getBinder y env))
  findUsedLocs env (Bind x b tm) 
    = assert_total (findUsedInBinder env b) ++ 
          dropHere (findUsedLocs (b :: env) tm)
  findUsedLocs env (App tm x) = findUsedLocs env tm ++ findUsedLocs env x
  findUsedLocs env _ = []
  
  findUsedInBinder : Env Term vars -> Binder (Term vars) -> 
                     List (x ** Elem x vars)
  findUsedInBinder env (Let _ val ty) 
    = findUsedLocs env val ++ findUsedLocs env ty
  findUsedInBinder env (PLet _ val ty)
    = findUsedLocs env val ++ findUsedLocs env ty
  findUsedInBinder env b = findUsedLocs env (binderType b)

-- Find the smallest subset of the environment which is needed to type check
-- the given term
export
findSubEnv : Env Term vars -> Term vars -> 
						 (vars' : List Name ** SubVars vars' vars)
findSubEnv env tm = mkShrink (findUsedLocs env tm)

-- Find the smallest subset of the current environment which is needed
-- for the scrutinee's type
-- See note above - if something goes wrong, it's safe to return the original
-- environment. We make no guarantee that the environment truly is the smallest
-- possible, but we'll make the best effort.
export
mkUsedEnv : Env Term vars -> Term vars -> Term vars ->
						(vars' : List Name ** 
							       (SubVars vars' vars, Env Term vars', Term vars', Term vars'))
mkUsedEnv env tm ty
   = let (_ ** sub) = mkShrink (findUsedLocs env tm ++ findUsedLocs env ty) in
         case shrinkEnv env sub of
              Nothing => (_ ** (SubRefl, env, tm, ty))
              Just env' =>
                   case shrinkTerm tm sub of
                        Nothing => (_ ** (SubRefl, env, tm, ty))
                        Just tm' =>
                             case shrinkTerm ty sub of
                                  Nothing => (_ ** (SubRefl, env, tm, ty))
                                  Just ty' => (_ ** (sub, env', tm', ty'))

public export
data CompatibleVars : List Name -> List Name -> Type where
     CompatPre : CompatibleVars xs xs
     CompatExt : CompatibleVars xs ys -> CompatibleVars (n :: xs) (m :: ys)

export
areVarsCompatible : (xs : List Name) -> (ys : List Name) -> 
                    Maybe (CompatibleVars xs ys)
areVarsCompatible [] [] = pure CompatPre
areVarsCompatible (x :: xs) (y :: ys)
    = do compat <- areVarsCompatible xs ys
         pure (CompatExt compat)
areVarsCompatible _ _ = Nothing


export
renameVars : CompatibleVars xs ys -> Term xs -> Term ys 
renameVars CompatPre tm = tm
renameVars prf (Local p) 
    = let (_ ** yprf) = renameLocal prf p in
          Local yprf
  where
    renameLocal : CompatibleVars xs ys -> Elem x xs -> (y ** Elem y ys)
    renameLocal CompatPre Here = (_ ** Here)
    renameLocal (CompatExt x) Here = (_ ** Here)
    renameLocal CompatPre (There later) = (_ ** There later)
    renameLocal (CompatExt x) (There later) 
        = let (_ ** prf) = renameLocal x later in
              (_ ** There prf)
renameVars prf (Ref nt fn) = Ref nt fn
renameVars prf (Bind x b tm) 
    = Bind x (assert_total (map (renameVars prf) b)) 
             (renameVars (CompatExt prf) tm)
renameVars prf (App fn arg) 
    = App (renameVars prf fn) (renameVars prf arg)
renameVars prf (PrimVal x) = PrimVal x
renameVars prf Erased = Erased
renameVars prf TType = TType

export
renameTop : (m : Name) -> Term (n :: vars) -> Term (m :: vars)
renameTop m tm = renameVars (CompatExt CompatPre) tm

export
apply : Term vars -> List (Term vars) -> Term vars
apply fn [] = fn
apply fn (arg :: args) = apply (App fn arg) args

-- Build a simple function type
export
fnType : Term vars -> Term vars -> Term vars
fnType arg scope = Bind (MN "_" 0) (Pi RigW Explicit arg) (weaken scope)

public export
data Unapply : Term vars -> Type where
     ArgsList : {f : Term vars} -> {args : List (Term vars)} ->
                Unapply (apply f args)

rewriteApp : (f : Term vars) -> (xs : List (Term vars)) -> 
             apply f (xs ++ [arg]) = App (apply f xs) arg
rewriteApp f [] = Refl
rewriteApp f (x :: xs) {arg} 
    = rewrite (rewriteApp (App f x) xs {arg}) in Refl

export
unapply : (tm : Term vars) -> Unapply tm
unapply (App fn arg) with (unapply fn)
  unapply (App (apply f xs) arg) | ArgsList 
      = rewrite sym (rewriteApp f xs {arg}) in 
                ArgsList {f} {args = xs ++ [arg]}
unapply tm = ArgsList {f = tm} {args = []}

export
getFnArgs : (tm : Term vars) -> (Term vars, List (Term vars))
getFnArgs tm with (unapply tm)
  getFnArgs (apply f args) | ArgsList = (f, args)

export
getFn : (tm : Term vars) -> Term vars
getFn tm = fst (getFnArgs tm)

export
getArgs : (tm : Term vars) -> List (Term vars)
getArgs tm = snd (getFnArgs tm)

export
getRefs : Term vars -> SortedSet
getRefs tm = getSet empty tm
  where
    getSet : SortedSet -> Term vars -> SortedSet
    getSet ns (Local y) = ns
    getSet ns (Ref nt fn) = insert fn ns
    getSet ns (Bind x (Let c val ty) tm) 
		   = assert_total $ getSet (getSet (getSet ns val) ty) tm
    getSet ns (Bind x (PLet c val ty) tm) 
		   = assert_total $ getSet (getSet (getSet ns val) ty) tm
    getSet ns (Bind x b tm) 
		   = assert_total $ getSet (getSet ns (binderType b)) tm
    getSet ns (App tm arg) 
		   = assert_total $ getSet (getSet ns tm) arg
    getSet ns (PrimVal x) = ns
    getSet ns Erased = ns
    getSet ns TType = ns

export
getPatternEnv : Env Term vars -> 
                (tm : Term vars) -> (ty : Term vars) ->
                (pvars ** (Env Term (pvars ++ vars),
                           Term (pvars ++ vars),
                           Term (pvars ++ vars)))
getPatternEnv {vars} env (Bind n (PVar c ty) sc) (Bind n' (PVTy c' ty') sc') 
    = case nameEq n n' of -- They should always be the same, but the
                          -- types don't tell us this. Better in any case to
                          -- rename n' to n since the de Bruijn indices will
                          -- match up okay.
           Nothing => ([] ** (env, Bind n (PVar c ty) sc, Bind n' (PVTy c' ty') sc'))
           Just Refl => let (more ** envtm) 
                              = getPatternEnv (extend n (PVar c ty) env) sc sc' in
                            (more ++ [n] ** rewrite sym (appendAssociative more [n] vars) in
                                                    envtm)
getPatternEnv env tm ty = ([] ** (env, tm, ty))

export
Show (Term vars) where
  show tm with (unapply tm)
    show (apply f args) | ArgsList = showApp f args
      where
        showCount : RigCount -> String
        showCount Rig0 = "0 "
        showCount Rig1 = "1 "
        showCount RigW = ""

        vCount : Elem x xs -> Nat
        vCount Here = 0
        vCount (There p) = 1 + vCount p

        showApp : Term vars -> List (Term vars) -> String
        -- It's for debugging purposes, so it's useful to mark resolved
        -- names somehow; resolved names are prefixed with a '!'
        showApp (Local {x} y) [] = "!" ++ show x -- ++ "[" ++ show (vCount y) ++ "]"
        showApp (Ref x fn) [] = show fn
        showApp (Bind n (Lam c x ty) sc) [] 
            = assert_total ("\\" ++ showCount c ++ show n ++ " : " ++ show ty ++ " => " ++ show sc)
        showApp (Bind n (Let c val ty) sc) [] 
            = assert_total ("let " ++ showCount c ++ show n ++ " : " ++ show ty ++ " = " ++
							               show val ++ " in " ++ show sc)
        showApp (Bind n (Pi c Explicit ty) sc) [] 
            = assert_total ("(" ++ showCount c ++ show n ++ " : " ++ show ty ++ ") -> " ++ show sc)
        showApp (Bind n (Pi c Implicit ty) sc) [] 
            = assert_total ("{" ++ showCount c ++ show n ++ " : " ++ show ty ++ "} -> " ++ show sc)
        showApp (Bind n (Pi c AutoImplicit ty) sc) [] 
            = assert_total ("{auto " ++ showCount c ++ show n ++ " : " ++ show ty ++ "} -> " ++ show sc)
        showApp (Bind n (PVar c ty) sc) [] 
            = assert_total ("pat " ++ showCount c ++ show n ++ " : " ++ show ty ++ " => " ++ show sc)
        showApp (Bind n (PLet c val ty) sc) [] 
            = assert_total ("plet " ++ showCount c ++ show n ++ " : " ++ show ty ++ " = " ++
							               show val ++ " in " ++ show sc)
        showApp (Bind n (PVTy c ty) sc) [] 
            = assert_total ("pty " ++ showCount c ++ show n ++ " : " ++ show ty ++ " => " ++ show sc)
        showApp (App f args) [] = "Can't happen!"
        showApp (PrimVal x) [] = show x
        showApp TType [] = "Type"
        showApp Erased [] = "__"
        showApp f [] = "[unknown thing]"
        -- below is only total because 'args' must be non-empty, so the
        -- totality checker won't see it
        showApp f args = "(" ++ assert_total (show f) ++ " " ++
                                assert_total (showSep " " (map show args))
                             ++ ")"

export
Show (Env Term vars) where
  show [] = "empty"
  show ((::) {x} b bs) = with Strings (show x ++ " " ++ show b ++ "; " ++ show bs)


-- Raw terms, not yet typechecked
public export
data Raw : Type where
     RVar : Name -> Raw
     RBind : Name -> Binder Raw -> Raw -> Raw
     RApp : Raw -> Raw -> Raw
     RPrimVal : Constant -> Raw
     RType : Raw

export
Show Raw where
  show (RVar n) = show n
  show (RBind n (Lam c x ty) sc)
       = "(\\" ++ show n ++ " : " ++ show ty ++ " => " ++ show sc ++ ")"
  show (RBind n (Pi c _ ty) sc)
       = "(" ++ show n ++ " : " ++ show ty ++ ") -> " ++ show sc
  show (RBind n (Let c val ty) sc)
       = "let " ++ show n ++ " : " ++ show ty ++ " = " ++ show val ++
         " in " ++ show sc
  show (RBind n (PVar c ty) sc)
       = "pat " ++ show n ++ " : " ++ show ty ++ ". " ++ show sc
  show (RBind n (PLet c val ty) sc)
       = "plet " ++ show n ++ " : " ++ show ty ++ " = " ++ show val ++
         " in " ++ show sc
  show (RBind n (PVTy c ty) sc)
       = "pty " ++ show n ++ " : " ++ show ty ++ ". " ++ show sc
  show (RApp f a)
       = "(" ++ show f ++ " " ++ show a ++ ")"
  show (RPrimVal p) = show p
  show RType = "Type"
  

export
rawApply : Raw -> List Raw -> Raw
rawApply fn [] = fn
rawApply fn (arg :: args) = rawApply (RApp fn arg) args

