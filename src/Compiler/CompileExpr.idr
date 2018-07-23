module Compiler.CompileExpr

import Core.CaseTree
import Core.CompileExpr
import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.Vect

%default covering

numArgs : Defs -> Term vars -> Nat
numArgs defs (Ref (DataCon tag arity) n) = arity
numArgs defs (Ref (TyCon tag arity) n) = arity
numArgs defs (Ref _ n)
    = case lookupDefExact n (gamma defs) of
           Just (PMDef _ args _ _) => length args
           Just (ExternDef arity) => arity
           Just (Builtin {arity} f) => arity
           _ => 0
numArgs _ _ = 0

weakenEl : (x ** List.Elem x ns) -> (x ** List.Elem x (a :: ns))
weakenEl (x ** p) = (x ** There p)

etaExpand : Int -> Nat -> CExp vars -> List (x ** List.Elem x vars) -> CExp vars
etaExpand i Z exp args = mkApp exp (map mkLocal (reverse args))
  where
    mkLocal : (x ** List.Elem x vars) -> CExp vars
    mkLocal (_ ** p) = CLocal p

    mkApp : CExp vars -> List (CExp vars) -> CExp vars
    mkApp tm [] = tm
    mkApp (CApp f args) args' = CApp f (args ++ args')
    mkApp (CCon n t args) args' = CCon n t (args ++ args')
    mkApp (CExtPrim p args) args' = CExtPrim p (args ++ args')
    mkApp tm args = CApp tm args
    
etaExpand i (S k) exp args
    = CLam (MN "x" i) (etaExpand (i + 1) k (weaken exp) 
                         ((_ ** Here) :: map weakenEl args))

expandToArity : Nat -> CExp vars -> List (CExp vars) -> CExp vars
-- No point in applying to anything
expandToArity _ CErased _ = CErased
-- Overapplied; apply everything as single arguments
expandToArity Z fn args = applyAll fn args
  where
    applyAll : CExp vars -> List (CExp vars) -> CExp vars
    applyAll fn [] = fn
    applyAll fn (a :: args) = applyAll (CApp fn [a]) args
expandToArity (S k) fn (a :: args) = expandToArity k (addArg fn a) args
  where
    addArg : CExp vars -> CExp vars -> CExp vars
    addArg (CApp fn args) a = CApp fn (args ++ [a])
    addArg (CCon n tag args) a = CCon n tag (args ++ [a])
    addArg (CExtPrim p args) a = CExtPrim p (args ++ [a])
    addArg f a = CApp f [a]
-- Underapplied, saturate with lambdas
expandToArity num fn [] = etaExpand 0 num fn []

cond : List (Lazy Bool, Lazy a) -> a -> a
cond [] def = def
cond ((x, y) :: xs) def = if x then y else cond xs def

-- Compiling external primitives, laziness, etc
specialApp : Defs -> Term vars -> List (CExp vars) -> Maybe (CExp vars)
specialApp defs (Ref _ n) args
    = cond
        [(isDelay n defs && not (isNil args), 
              case reverse (filter notErased args) of
                   [a] => Just (CDelay a)
                   _ => Nothing),
         (isForce n defs && not (isNil args),
              case reverse (filter notErased args) of
                   [a] => Just (CForce a)
                   _ => Nothing)]
        Nothing
  where
    notErased : CExp vars -> Bool
    notErased CErased = False
    notErased _ = True

specialApp defs f args = Nothing

mutual
  toCExpTm : Defs -> Name -> Term vars -> CExp vars
  toCExpTm defs n (Local prf) = CLocal prf
  toCExpTm defs n (Ref (DataCon tag arity) fn) = CCon fn tag []
  toCExpTm defs n (Ref (TyCon tag arity) fn) = CErased
  toCExpTm defs n (Ref _ fn) = CRef fn
  toCExpTm defs n (Bind x (Lam _ _ _) sc)
      = CLam x (toCExp defs n sc)
  toCExpTm defs n (Bind x (Let _ val _) sc)
      = CLet x (toCExp defs n val) (toCExp defs n sc)
  toCExpTm defs n (Bind x b tm) = CErased
  -- We'd expect this to have been dealt with in toCExp, but for completeness...
  toCExpTm defs n (App tm arg) = CApp (toCExp defs n tm) [toCExp defs n arg]
  toCExpTm defs n (PrimVal c) = CPrimVal c
  toCExpTm defs n Erased = CErased
  toCExpTm defs n TType = CErased

  toCExp : Defs -> Name -> Term vars -> CExp vars
  toCExp defs n tm with (unapply tm)
    toCExp defs n (apply f args) | ArgsList 
        = let args' = map (toCExp defs n) args in
              maybe (expandToArity (numArgs defs f) (toCExpTm defs n f) args')
                    id
                    (specialApp defs f args')

mutual
  toCAlt : Defs -> Name -> CaseAlt vars -> CAlt vars
  toCAlt defs n (ConCase x tag args sc) = CConCase x tag args (toCExpTree defs n sc)
  toCAlt defs n (ConstCase x sc) = CConstCase x (toCExpTree defs n sc)
  toCAlt defs n (DefaultCase sc) = CDefaultCase (toCExpTree defs n sc)

  toCExpTree : Defs -> Name -> CaseTree vars -> CExp vars
  toCExpTree defs n (Case x scTy alts) 
      = CCase (CLocal x) (map (toCAlt defs n) alts)
  toCExpTree defs n (STerm tm) = toCExp defs n tm
  toCExpTree defs n (Unmatched msg) = CCrash msg 
  toCExpTree defs n Impossible = CCrash $ "Impossible case encountered in " ++ show n

-- Need this for ensuring that argument list matches up to operator arity for
-- builtins
data ArgList : Nat -> List Name -> Type where
     NoArgs : ArgList Z []
     ConsArg : (a : Name) -> ArgList k as -> ArgList (S k) (a :: as)

mkArgList : Int -> (n : Nat) -> (ns ** ArgList n ns)
mkArgList i Z = (_ ** NoArgs)
mkArgList i (S k) 
    = let (_ ** rec) = mkArgList (i + 1) k in
          (_ ** ConsArg (MN "arg" i) rec)

toCDef : {auto c : Ref Ctxt Defs} -> Name -> Def -> Core annot CDef
toCDef n None
    = pure $ MkError $ CCrash ("Encountered undefined name " ++ show n)
toCDef n (PMDef _ args _ tree)
    = pure $ MkFun _ (toCExpTree !(get Ctxt) n tree) 
toCDef n (ExternDef arity)
    = let (ns ** args) = mkArgList 0 arity in
          pure $ MkFun _ (CExtPrim n (map toArgExp (getVars args)))
  where
    toArgExp : (x ** List.Elem x ns) -> CExp ns
    toArgExp (x ** p) = CLocal p

    getVars : ArgList k ns -> List (x ** List.Elem x ns)
    getVars NoArgs = []
    getVars (ConsArg a rest) = (a ** Here) :: map weakenEl (getVars rest)
toCDef n (Builtin {arity} op)
    = let (ns ** args) = mkArgList 0 arity in
          pure $ MkFun _ (COp op (map toArgExp (getVars args)))
  where
    toArgExp : (x ** List.Elem x ns) -> CExp ns
    toArgExp (x ** p) = CLocal p

    getVars : ArgList k ns -> Vect k (x ** List.Elem x ns)
    getVars NoArgs = []
    getVars (ConsArg a rest) = (a ** Here) :: map weakenEl (getVars rest)
toCDef n (DCon _ _ _)
    = throw (InternalError ("Can't compile constructors directly " ++ show n))
toCDef n (TCon _ _ _ _ _)
    = throw (InternalError ("Can't compile constructors directly " ++ show n))
-- We do want to be able to compile these, but also report an error at run time
-- (and, TODO: warn at compile time)
toCDef n (Hole _ _ _)
    = pure $ MkError $ CCrash ("Encountered unimplemented hole " ++ show n)
toCDef n (Guess _ _)
    = pure $ MkError $ CCrash ("Encountered constrained hole " ++ show n)
toCDef n (BySearch _ _)
    = pure $ MkError $ CCrash ("Encountered incomplete proof search " ++ show n)
toCDef n def
    = pure $ MkError $ CCrash ("Encountered uncompilable name " ++ show (n, def))

export
compileDef : {auto c : Ref Ctxt Defs} -> Name -> Core annot ()
compileDef n
    = do defs <- get Ctxt
         case lookupDefExact n (gamma defs) of
              Just d => do ce <- toCDef n d
                           setCompiled n ce
              Nothing => throw (InternalError ("Trying to compile unknown name " ++ show n))
