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

-- for typecase
export
constTag : Constant -> Int
-- 1 = ->, 2 = Type
constTag IntType = 3
constTag IntegerType = 4
constTag StringType = 5
constTag CharType = 6
constTag DoubleType = 7
constTag WorldType = 8
constTag _ = 0

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
     StrIndex : PrimFn 2
     StrCons : PrimFn 2
     StrAppend : PrimFn 2
     StrReverse : PrimFn 1
     StrSubstr : PrimFn 3

     Cast : Constant -> Constant -> PrimFn 1
     BelieveMe : PrimFn 3

export
Show (PrimFn arity) where
  show (Add ty) = "+" ++ show ty
  show (Sub ty) = "-" ++ show ty
  show (Mul ty) = "*" ++ show ty
  show (Div ty) = "/" ++ show ty
  show (Mod ty) = "%" ++ show ty
  show (Neg ty) = "neg " ++ show ty
  show (LT ty) = "<" ++ show ty
  show (LTE ty) = "<=" ++ show ty
  show (EQ ty) = "==" ++ show ty
  show (GTE ty) = ">=" ++ show ty
  show (GT ty) = ">" ++ show ty
  show StrLength = "op_strlen"
  show StrHead = "op_strhead"
  show StrTail = "op_strtail"
  show StrIndex = "op_strindex"
  show StrCons = "op_strcons"
  show StrAppend = "++"
  show StrReverse = "op_strrev"
  show StrSubstr = "op_strsubstr"
  show (Cast x y) = "cast-" ++ show x ++ "-" ++ show y
  show BelieveMe = "believe_me"

public export
data PiInfo = Implicit | Explicit | AutoImplicit

export
Eq PiInfo where
  (==) Implicit Implicit = True
  (==) Explicit Explicit = True
  (==) AutoImplicit AutoImplicit = True
  (==) _ _ = False

export
Show PiInfo where
  show Implicit = "Implicit"
  show Explicit = "Explicit"
  show AutoImplicit = "AutoImplicit"

-- Multiplicities on binders, for checking linear and erased types
-- TODO: This doesn't actually do anything yet, but I wanted to add it to
-- the representation early so that there's less to change in the data types
-- Needs updates in: Core.Typecheck and TTImp.Elab.Term, at least, and
-- dealing with how to bind pattern names in TTImp.Elab.State

-- Also need updating RawImp and PTerm syntax
public export
data RigCount = Rig0 
							| Rig1 Bool -- True = 'borrowed', i.e. call doesn't count as
			                    -- spending the name
			        | RigW

export
rig1 : RigCount
rig1 = Rig1 False

export
rigb : RigCount
rigb = Rig1 True

export
isLinear : RigCount -> Bool
isLinear (Rig1 _) = True
isLinear _ = False

export
Eq RigCount where
  (==) Rig0 Rig0 = True
  (==) (Rig1 x) (Rig1 x') = x == x'
  (==) RigW RigW = True
  (==) _ _ = False

export
Ord RigCount where
  compare Rig0 Rig0 = EQ
  compare Rig0 (Rig1 _) = LT
  compare Rig0 RigW = LT

  compare (Rig1 _) Rig0 = GT
  compare (Rig1 x) (Rig1 x') = compare x x'
  compare (Rig1 _) RigW = LT

  compare RigW Rig0 = GT
  compare RigW (Rig1 _) = GT
  compare RigW RigW = EQ

export
Show RigCount where
  show Rig0 = "Rig0"
  show (Rig1 False) = "Rig1"
  show (Rig1 True) = "RigB"
  show RigW = "RigW"

export
rigPlus : RigCount -> RigCount -> RigCount
rigPlus Rig0 Rig0 = Rig0
rigPlus Rig0 (Rig1 x) = Rig1 x
rigPlus Rig0 RigW = RigW
rigPlus (Rig1 x) Rig0 = Rig1 x
rigPlus (Rig1 _) (Rig1 _) = RigW
rigPlus (Rig1 _) RigW = RigW
rigPlus RigW Rig0 = RigW
rigPlus RigW (Rig1 _) = RigW
rigPlus RigW RigW = RigW

export
rigMult : RigCount -> RigCount -> RigCount
rigMult Rig0 Rig0 = Rig0
rigMult Rig0 (Rig1 _) = Rig0
rigMult Rig0 RigW = Rig0
rigMult (Rig1 _) Rig0 = Rig0
rigMult (Rig1 x) (Rig1 x') = Rig1 (x || x')
rigMult (Rig1 _) RigW = RigW
rigMult RigW Rig0 = Rig0
rigMult RigW (Rig1 _) = RigW
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
        
showCount : RigCount -> String
showCount Rig0 = "0 "
showCount (Rig1 False) = "1 "
showCount (Rig1 True) = "& "
showCount RigW = ""
  
Show ty => Show (Binder ty) where
	show (Lam c _ t) = "\\" ++ showCount c ++ show t
	show (Pi c _ t) = "Pi " ++ showCount c ++ show t
	show (Let c v t) = "let " ++ showCount c ++ show v ++ " : " ++ show t
	show (PVar c t) = "pat " ++ showCount c ++ show t
	show (PLet c v t) = "plet " ++ showCount c ++ show v ++ ": " ++ show t
	show (PVTy c t) = "pty " ++ showCount c ++ show t

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
     Local : Maybe RigCount -> Elem x vars -> Term vars
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
data PartialReason 
       = NotStrictlyPositive 
       | BadCall (List Name)
       | RecPath (List Name)

export
Show PartialReason where
  show NotStrictlyPositive = "not strictly positive"
  show (BadCall [n]) 
	   = "not terminating due to call to " ++ show n
  show (BadCall ns) 
	   = "not terminating due to calls to " ++ showSep ", " (map show ns) 
  show (RecPath ns) 
	   = "not terminating due to recursive path " ++ showSep " -> " (map show ns) 

public export
data Terminating
       = Unchecked
       | IsTerminating
       | NotTerminating PartialReason

export
Show Terminating where
  show Unchecked = "not yet checked"
  show IsTerminating = "terminating"
  show (NotTerminating p) = show p

public export
data Covering 
       = IsCovering
       | MissingCases (List (Term []))
       | NonCoveringCall (List Name)

export
Show Covering where
  show IsCovering = "covering"
  show (MissingCases c) = "not covering all cases"
  show (NonCoveringCall [f]) 
     = "not covering due to call to function " ++ show f
  show (NonCoveringCall cs) 
     = "not covering due to calls to functions " ++ showSep ", " (map show cs)

-- Totality status of a definition. We separate termination checking from
-- coverage checking.
public export
record Totality where
     constructor MkTotality
     isTerminating : Terminating
     isCovering : Covering

export
Show Totality where
  show tot
    = let t	= isTerminating tot
          c = isCovering tot in
        showTot t c
    where
      showTot : Terminating -> Covering -> String
      showTot IsTerminating IsCovering = "total"
      showTot IsTerminating c = show c
      showTot t IsCovering = show t
      showTot t c = show c ++ "; " ++ show t

export
unchecked : Totality
unchecked = MkTotality Unchecked IsCovering

export
isTotal : Totality
isTotal = MkTotality Unchecked IsCovering

export
notCovering : Totality
notCovering = MkTotality Unchecked (MissingCases [])

export
sameVar : Elem x xs -> Elem y xs -> Bool
sameVar Here Here = True
sameVar (There p1) (There p2) = sameVar p1 p2
sameVar _ _ = False

export
Eq a => Eq (Binder a) where
  (Lam c p ty) == (Lam c' p' ty') = c == c' && p == p' && ty == ty'
  (Let c v ty) == (Let c' v' ty') = c == c' && v == v' && ty == ty'
  (Pi c p ty) == (Pi c' p' ty') = c == c' && p == p' && ty == ty'
  (PVar c ty) == (PVar c' ty') = c == c' && ty == ty'
  (PLet c v ty) == (PLet c' v' ty') = c == c' && v == v' && ty == ty'
  (PVTy c ty) == (PVTy c' ty') = c == c' && ty == ty'
  _ == _ = False

export
Eq (Term vars) where
  (Local c p) == (Local c' p')      = sameVar p p'
  (Ref _ fn) == (Ref _ fn')         = fn == fn'
  (Bind x b sc) == (Bind x' b' sc') 
      -- We could set this up a bit differently and not need the 'believe_me'
      -- if we passed through a proof that context lengths were equal.
      -- Maybe someone will tidy it up one day. I promise it's safe :).
	    = assert_total (b == b') && sc == believe_me sc'
  (App f a) == (App f' a')          = f == f' && a == a'
  (PrimVal c) == (PrimVal c')       = c == c'
  Erased == Erased                  = True
  TType == TType                    = True
  _ == _                            = False

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

export
bindEnv : Env Term vars -> (tm : Term vars) -> ClosedTerm
bindEnv [] tm = tm
bindEnv (b :: env) tm 
    = bindEnv env (Bind _ b tm)

-- Also define Values here - NF represents a term in head normal form.
-- That is - the top level constructor is known but the arguments aren't
-- evaluted. Terms are evaluated to NF in Core.Normalise.

public export
record EvalOpts where
  constructor MkEvalOpts
  holesOnly : Bool -- only evaluate hole solutions
  evalAll : Bool -- evaluate everything, including private names
  tcInline : Bool -- inline for totality checking
  fuel : Maybe Nat -- Limit for recursion depth

export
defaultOpts : EvalOpts
defaultOpts = MkEvalOpts False False False (Just 100000)

export
withHoles : EvalOpts
withHoles = MkEvalOpts True False False (Just 100)

export
withAll : EvalOpts
withAll = MkEvalOpts False True False Nothing

export
tcOnly : EvalOpts
tcOnly = MkEvalOpts True False True (Just 100)


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
       MkClosure : (opts : EvalOpts) ->
                   LocalEnv free vars -> 
                   Env Term free ->
                   Term (vars ++ free) -> Closure free
       MkNFClosure : NF free -> Closure free

  -- The head of a value: things you can apply arguments to
  public export
  data NHead : List Name -> Type where
       NLocal : Maybe RigCount -> Elem x vars -> NHead vars
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
export
insertElem : Elem x (outer ++ inner) -> Elem x (outer ++ n :: inner)
insertElem {outer = []} p = There p
insertElem {outer = (x :: xs)} Here = Here
insertElem {outer = (y :: xs)} (There later) 
   = There (insertElem {outer = xs} later)

export
thin : (n : Name) -> Term (outer ++ inner) -> Term (outer ++ n :: inner)
thin n (Local r prf) = Local r (insertElem prf)
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
insertNames ns (Local r prf) = Local r (insertElemNames ns prf)
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
-- What Could Possibly Go Wrong?
-- This relies on the runtime representation of the term being the same
-- after embedding! It is just an identity function at run time, though, and
-- we don't need its definition at compile time, so let's do it...
elemExtend p = believe_me p
{- Original definition:
elemExtend Here = Here
elemExtend (There later) = There (elemExtend later)
-}

export
embed : Term vars -> Term (vars ++ more)
-- As above, it's an identity function at run time
embed tm = believe_me tm
{- Original definition:
embed (Local r prf) = Local r (elemExtend prf)
embed (Ref x fn) = Ref x fn
embed (Bind x b tm) = Bind x (assert_total (map embed b)) (embed tm)
embed (App f a) = App (embed f) (embed a)
embed (PrimVal x) = PrimVal x
embed Erased = Erased
embed TType = TType
-}

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

revOnto : (xs, vs : _) -> reverseOnto xs vs = reverse vs ++ xs
revOnto xs [] = Refl
revOnto xs (v :: vs) 
    = rewrite revOnto (v :: xs) vs in 
        rewrite appendAssociative (reverse vs) [v] xs in
				  rewrite revOnto [v] vs in Refl

revNs : (vs, ns : List a) -> reverse ns ++ reverse vs = reverse (vs ++ ns)
revNs [] ns = rewrite appendNilRightNeutral (reverse ns) in Refl
revNs (v :: vs) ns 
    = rewrite revOnto [v] vs in
        rewrite revOnto [v] (vs ++ ns) in
          rewrite sym (revNs vs ns) in
            rewrite appendAssociative (reverse ns) (reverse vs) [v] in
              Refl
	
-- Weaken by all the names at once at the end, to save multiple traversals
-- in big environments
-- Also reversing the names at the end saves significant time over concatenating
-- when environments get fairly big.
export
getBinderUnder : Weaken tm => 
                 (ns : List Name) -> 
                 Elem x vars -> Env tm vars -> 
                 Binder (tm (reverse ns ++ vars))
getBinderUnder {vars = v :: vs} ns Here (b :: env) 
    = rewrite appendAssociative (reverse ns) [v] vs in
			 rewrite revNs [v] ns in
         map (weakenNs (reverse (v :: ns))) b
getBinderUnder {vars = v :: vs} ns (There later) (b :: env) 
    = rewrite appendAssociative (reverse ns) [v] vs in
			 rewrite revNs [v] ns in
         getBinderUnder (v :: ns) later env

export
getBinder : Weaken tm => Elem x vars -> Env tm vars -> Binder (tm vars)
getBinder el env = getBinderUnder [] el env

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

mkLocal : (x : Name) -> 
          Maybe RigCount -> Elem new (later ++ new :: vars) ->
          Term (later ++ vars) -> Term (later ++ new :: vars)
mkLocal x _ loc (Local r prf) = Local r (addVar prf)
mkLocal x r loc (Ref y fn) with (x == fn)
  mkLocal x r loc (Ref y fn) | True = Local r loc
  mkLocal x r loc (Ref y fn) | False = Ref y fn
mkLocal {later} x r loc (Bind y b tm) 
    = Bind y (assert_total (map (mkLocal x r loc) b)) 
             (mkLocal {later = y :: later} x r (There loc) tm)
mkLocal x r loc (App f a) = App (mkLocal x r loc f) (mkLocal x r loc a)
mkLocal x r loc (PrimVal y) = PrimVal y
mkLocal x r loc Erased = Erased
mkLocal x r loc TType = TType

-- Replace any reference to 'x' with a locally bound name 'new'
export
refToLocal : Maybe RigCount ->
						 (x : Name) -> (new : Name) -> Term vars -> Term (new :: vars)
refToLocal r x new tm = mkLocal {later = []} x r Here tm

-- Oops, no DecEq for Name, so we need this
export
isVar : (n : Name) -> (ns : List Name) -> Maybe (Elem n ns)
isVar n [] = Nothing
isVar n (m :: ms) 
    = case nameEq n m of
           Nothing => do p <- isVar n ms
                         pure (There p)
           Just Refl => pure Here

-- Replace any Ref Bound in a type with appropriate local
export
resolveRefs : (vars : List Name) -> Term vars -> Term vars
resolveRefs vars (Ref Bound n)
    = case isVar n vars of
           Just prf => Local Nothing prf
           _ => Ref Bound n
resolveRefs vars (Bind x b sc)
    = Bind x (assert_total (map (resolveRefs vars) b))
             (resolveRefs (x :: vars) sc)
resolveRefs vars (App f a) = App (resolveRefs vars f) (resolveRefs vars a)
resolveRefs vars tm = tm

-- Substitute some explicit terms for names in a term, and remove those
-- names from the scope
namespace SubstEnv
  data SubstEnv : List Name -> List Name -> Type where
       Nil : SubstEnv [] vars
       (::) : Term vars -> 
              SubstEnv ds vars -> SubstEnv (d :: ds) vars

  findDrop : Maybe RigCount -> Elem x (drop ++ vars) -> SubstEnv drop vars -> Term vars
  findDrop {drop = []} r var env = Local r var
  findDrop {drop = (x :: xs)} r Here (tm :: env) = tm
  findDrop {drop = (x :: xs)} r (There later) (tm :: env) = findDrop r later env

  find : Maybe RigCount -> Elem x (outer ++ (drop ++ vars)) ->
         SubstEnv drop vars ->
         Term (outer ++ vars)
  find {outer = []} r var env = findDrop r var env
  find {outer = (x :: xs)} r Here env = Local r Here
  find {outer = (x :: xs)} r (There later) env = weaken (find r later env)

  substEnv : SubstEnv drop vars -> Term (outer ++ (drop ++ vars)) -> 
             Term (outer ++ vars)
  substEnv env (Local r prf) = find r prf env
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
substName x new (Local r p) = Local r p
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
abstractFullEnvType (Pi c e ty :: env) tm 
    = abstractFullEnvType env (Bind _ (Pi c e ty) tm)
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

export
subElem : Elem x xs -> SubVars ys xs -> Maybe (Elem x ys)
subElem prf SubRefl = Just prf
subElem Here (DropCons ds) = Nothing
subElem (There later) (DropCons ds) 
       = Just !(subElem later ds)
subElem Here (KeepCons ds) = Just Here
subElem (There later) (KeepCons ds) 
       = Just (There !(subElem later ds))

export
changeVar : (old : Elem x vs) -> (new : Elem y vs) -> Term vs -> Term vs
changeVar old new (Local r y) 
    = if sameVar old y
         then Local r new
         else Local r y
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
        b' = case bindervs of
                  Let c val ty => Let c val ty
                  _ => Pi (multiplicity b) Explicit (binderType bindervs)
        btm = Bind x b' 
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
        b' = case bindervs of
                  Let c val ty => Let c val ty
                  _ => Pi (multiplicity b) Explicit (binderType bindervs)
        btm = Bind x b' 
                   (changeVar (findLater (x :: done)) Here (weaken tm)) in
        rewrite appendAssociative done [x] vars in
                absSmaller {done = done ++ [x]} env sub
                    (rewrite sym (appendAssociative done [x] vars) in btm)

-- For any variable *not* in vs', re-abstract over it in the term
export
absOthers : Env Term vs -> SubVars vs' vs -> 
					 Term (done ++ vs) -> Term (done ++ vs)
absOthers _ SubRefl tm = tm
absOthers {done} {vs = x :: vars} (b :: env) (KeepCons sub) tm 
  = rewrite appendAssociative done [x] vars in
            absOthers {done = done ++ [x]} env sub
               (rewrite sym (appendAssociative done [x] vars) in tm)
absOthers {done} {vs = x :: vars} (b :: env) (DropCons sub) tm
  = let bindervs : Binder (Term (done ++ (x :: vars)))
                      = rewrite appendAssociative done [x] vars in
                                map (weakenNs (done ++ [x])) b
        b' = case bindervs of
                  Let c val ty => Let c val ty
                  _ => Pi (multiplicity b) Explicit (binderType bindervs)
        btm = Bind x b' 
                   (changeVar (findLater (x :: done)) Here (weaken tm)) in
        rewrite appendAssociative done [x] vars in
                absOthers {done = done ++ [x]} env sub
                    (rewrite sym (appendAssociative done [x] vars) in btm)

-- Would be handy if binders were Traversable...

mutual
  export
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
  shrinkTerm (Local r y) subprf = Just (Local r !(subElem y subprf))
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

weakenVars : List (x ** Elem x xs) -> List (x ** Elem x (n :: xs))
weakenVars [] = []
weakenVars ((_ ** p) :: xs) = (_ ** There p) :: weakenVars xs

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
      
merge : {vs : List Name} ->
				List (x ** Elem x vs) -> List (x ** Elem x vs) -> List (x ** Elem x vs)
merge [] xs = xs
merge ((_ ** v) :: vs) xs
		= merge vs ((_ ** v) :: filter (\p => not (sameVar v (DPair.snd p))) xs)

mutual
  vCount : Elem x xs -> Nat
  vCount Here = Z
  vCount (There p) = S (vCount p)

  dropS : List Nat -> List Nat
  dropS [] = []
  dropS (Z :: xs) = dropS xs
  dropS (S p :: xs) = p :: dropS xs

	-- Quicker, if less safe, to store variables as a Nat, for quick comparison
  findUsed : Env Term vars -> List Nat -> Term vars -> List Nat
  findUsed env used (Local r y) 
    = let yn = vCount y in
					if elem yn used 
						 then used
						 else	assert_total (findUsedInBinder env (yn :: used)
																								 (getBinder y env))
  findUsed env used (Bind x b tm) 
    = assert_total $
        dropS (findUsed (b :: env)
                        (map S (findUsedInBinder env used b))
                        tm)
  findUsed env used (App fn arg) 
    = findUsed env (findUsed env used fn) arg
  findUsed env used _ = used
  
  findUsedInBinder : Env Term vars -> List Nat ->
										 Binder (Term vars) -> List Nat
  findUsedInBinder env used (Let _ val ty) 
    = findUsed env (findUsed env used val) ty
  findUsedInBinder env used (PLet _ val ty)
    = findUsed env (findUsed env used val) ty
  findUsedInBinder env used b = findUsed env used (binderType b)

toElem : (vars : List Name) -> Nat -> Maybe (x ** Elem x vars)
toElem (v :: vs) Z = Just (_ ** Here)
toElem (v :: vs) (S k)
   = do (_ ** prf) <- toElem vs k 
        Just (_ ** There prf)
toElem _ _ = Nothing

export
findUsedLocs : Env Term vars -> Term vars -> List (x ** Elem x vars)
findUsedLocs env tm 
    = mapMaybe (toElem _) (findUsed env [] tm)


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
renameVars prf (Local r p) 
    = let (_ ** yprf) = renameLocal prf p in
          Local r yprf
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
renameEnv : CompatibleVars xs ys -> Env Term xs -> Env Term ys
renameEnv CompatPre env = env
renameEnv (CompatExt p) (b :: bs)
    = map (renameVars p) b :: renameEnv p bs

export
apply : Term vars -> List (Term vars) -> Term vars
apply fn [] = fn
apply fn (arg :: args) = apply (App fn arg) args

-- Build a simple function type
export
fnType : Term vars -> Term vars -> Term vars
fnType arg scope = Bind (MN "_" 0) (Pi RigW Explicit arg) (weaken scope)

export
linFnType : Term vars -> Term vars -> Term vars
linFnType arg scope = Bind (MN "_" 0) (Pi (Rig1 False) Explicit arg) (weaken scope)

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
getFnArgs tm = getFA [] tm
  where
    getFA : List (Term vars) -> Term vars -> (Term vars, List (Term vars))
    getFA args (App f a) = getFA (a :: args) f
    getFA args tm = (tm, args)

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
    getSet ns (Local r y) = ns
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
        vCount : Elem x xs -> Nat
        vCount Here = 0
        vCount (There p) = 1 + vCount p

        showApp : Term vars -> List (Term vars) -> String
        -- It's for debugging purposes, so it's useful to mark resolved
        -- names somehow; resolved names are displayed with their de Bruijn
				-- index count
        showApp (Local {x} r y) [] = show x ++ "[" ++ show (vCount y) ++ "]"
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
  show ((::) {x} b bs) 
	    = with Strings (show x ++ " " ++ show b ++ "; " ++ show bs)


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

