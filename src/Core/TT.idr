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
data Constant = I Integer
              | IntType

export
constantEq : (x, y : Constant) -> Maybe (x = y)
constantEq (I x) (I y) = case decEq x y of
                              Yes Refl => Just Refl
                              No contra => Nothing
constantEq IntType IntType = Just Refl
constantEq _ _ = Nothing

export
Show Constant where
  show (I x) = show x
  show IntType = "Int"

export
Eq Constant where
   (I x) == (I y) = x == y
   IntType == IntType = True
   _ == _ = False

public export
data PiInfo = Implicit | Explicit | AutoImplicit | Constraint

export
Eq PiInfo where
  (==) Implicit Implicit = True
  (==) Explicit Explicit = True
  (==) AutoImplicit AutoImplicit = True
  (==) Constraint Constraint = True
  (==) _ _ = False

public export
data Binder : Type -> Type where
     Lam : PiInfo -> (ty : type) -> Binder type
     Let : (val : type) -> (ty : type) -> Binder type
     Pi : PiInfo -> (ty : type) -> Binder type
     PVar : (ty : type) -> Binder type
     PVTy : (ty : type) -> Binder type

export
binderType : Binder tm -> tm
binderType (Lam x ty) = ty
binderType (Let val ty) = ty
binderType (Pi x ty) = ty
binderType (PVar ty) = ty
binderType (PVTy ty) = ty

export
setType : Binder tm -> tm -> Binder tm
setType (Lam x _) ty = Lam x ty
setType (Let val _) ty = Let val ty
setType (Pi x _) ty = Pi x ty
setType (PVar _) ty = PVar ty
setType (PVTy _) ty = PVTy ty

export
Functor Binder where
  map func (Lam x ty) = Lam x (func ty)
  map func (Let val ty) = Let (func val) (func ty)
  map func (Pi x ty) = Pi x (func ty)
  map func (PVar ty) = PVar (func ty)
  map func (PVTy ty) = PVTy (func ty)

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

%name Env env

export
defined : (n : Name) -> Env Term vars -> Maybe (Elem n vars)
defined n [] = Nothing
defined {vars = x :: xs} n (b :: env) with (nameEq x n)
  defined {vars = n :: xs} n (b :: env) | (Just Refl) 
      = Just Here
  defined {vars = x :: xs} n (b :: env) | Nothing 
      = Just (There !(defined n env))

-- Make a type which abstracts over an environment
export
abstractEnvType : Env Term vars -> (tm : Term vars) -> ClosedTerm
abstractEnvType [] tm = tm
abstractEnvType (b :: env) tm 
    = abstractEnvType env (Bind _ (Pi Explicit (binderType b)) tm)


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

-- Would be handy if binders were Traversable...

mutual
  shrinkBinder : Binder (Term vars) -> SubVars newvars vars -> 
                 Maybe (Binder (Term newvars))
  shrinkBinder (Lam x ty) subprf 
      = Just (Lam x !(shrinkTerm ty subprf))
  shrinkBinder (Let val ty) subprf 
      = Just (Let !(shrinkTerm val subprf)
                  !(shrinkTerm ty subprf))
  shrinkBinder (Pi x ty) subprf 
      = Just (Pi x !(shrinkTerm ty subprf))
  shrinkBinder (PVar ty) subprf 
      = Just (PVar !(shrinkTerm ty subprf))
  shrinkBinder (PVTy ty) subprf 
      = Just (PVTy !(shrinkTerm ty subprf))

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
getFn : (tm : Term vars) -> Term vars
getFn tm with (unapply tm)
  getFn (apply f args) | ArgsList = f

export
getArgs : (tm : Term vars) -> List (Term vars)
getArgs tm with (unapply tm)
  getArgs (apply f args) | ArgsList = args

export
getRefs : Term vars -> SortedSet
getRefs tm = getSet empty tm
  where
    getSet : SortedSet -> Term vars -> SortedSet
    getSet ns (Local y) = ns
    getSet ns (Ref nt fn) = insert fn ns
    getSet ns (Bind x (Let val ty) tm) 
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
getPatternEnv {vars} env (Bind n (PVar ty) sc) (Bind n' (PVTy ty') sc') 
    = case nameEq n n' of -- TODO: They should always be the same, but the
                          -- types don't tell us this. Better in any case to
                          -- rename n' to n since the de Bruijn indices will
                          -- match up okay.
           Nothing => ([] ** (env, Bind n (PVar ty) sc, Bind n' (PVTy ty') sc'))
           Just Refl => let (more ** envtm) 
                              = getPatternEnv (extend n (PVar ty) env) sc sc' in
                            (more ++ [n] ** rewrite sym (appendAssociative more [n] vars) in
                                                    envtm)
getPatternEnv env tm ty = ([] ** (env, tm, ty))

export
Show (Term vars) where
  show tm with (unapply tm)
    show (apply f args) | ArgsList = showApp f args
      where
        showApp : Term vars -> List (Term vars) -> String
        showApp (Local {x} y) [] = show x
        showApp (Ref x fn) [] = show fn
        showApp (Bind n (Lam x ty) sc) [] 
            = assert_total ("\\" ++ show n ++ " : " ++ show ty ++ " => " ++ show sc)
        showApp (Bind n (Pi Explicit ty) sc) [] 
            = assert_total ("(" ++ show n ++ " : " ++ show ty ++ ") -> " ++ show sc)
        showApp (Bind n (Pi Implicit ty) sc) [] 
            = assert_total ("{" ++ show n ++ " : " ++ show ty ++ "} -> " ++ show sc)
        showApp (Bind n (PVar ty) sc) [] 
            = assert_total ("pat " ++ show n ++ " : " ++ show ty ++ " => " ++ show sc)
        showApp (Bind n (PVTy ty) sc) [] 
            = assert_total ("pty " ++ show n ++ " : " ++ show ty ++ " => " ++ show sc)
        showApp (App f args) [] = "Can't happen!"
        showApp (PrimVal x) [] = show x
        showApp TType [] = "Type"
        showApp Erased [] = "[__]"
        showApp f [] = "[unknown thing]"
        -- below is only total because 'args' must be non-empty, so the
        -- totality checker won't see it
        showApp f args = "(" ++ assert_total (show f) ++ " " ++
                                assert_total (showSep " " (map show args))
                             ++ ")"

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
  show (RBind n (Lam x ty) sc)
       = "(\\" ++ show n ++ " : " ++ show ty ++ " => " ++ show sc ++ ")"
  show (RBind n (Pi _ ty) sc)
       = "(" ++ show n ++ " : " ++ show ty ++ ") -> " ++ show sc
  show (RBind n (Let val ty) sc)
       = "let " ++ show n ++ " : " ++ show ty ++ " = " ++ show val ++
         " in " ++ show sc
  show (RBind n (PVar ty) sc)
       = "pat " ++ show n ++ " : " ++ show ty ++ ". " ++ show sc
  show (RBind n (PVTy ty) sc)
       = "pty " ++ show n ++ " : " ++ show ty ++ ". " ++ show sc
  show (RApp f a)
       = "(" ++ show f ++ " " ++ show a ++ ")"
  show (RPrimVal p) = show p
  show RType = "Type"
  

export
rawApply : Raw -> List Raw -> Raw
rawApply fn [] = fn
rawApply fn (arg :: args) = rawApply (RApp fn arg) args
