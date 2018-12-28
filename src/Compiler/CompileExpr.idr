module Compiler.CompileExpr

import Core.CaseTree
import public Core.CompileExpr
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
           Just (PMDef _ args _ _ _) => length args
           Just (ExternDef arity) => arity
           Just (Builtin {arity} f) => arity
           _ => 0
numArgs _ tm = 0

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
  toCExpTm defs n (Local _ prf) = CLocal prf
  toCExpTm defs n (Ref (DataCon tag arity) fn) = CCon fn tag []
  toCExpTm defs n (Ref (TyCon tag arity) fn) = CCon fn tag []
  toCExpTm defs n (Ref _ fn) = CApp (CRef fn) []
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
  conCases : Defs -> Name -> List (CaseAlt vars) -> List (CConAlt vars)
  conCases defs n [] = []
  conCases defs n (ConCase x tag args sc :: ns)
      = MkConAlt x tag args (toCExpTree defs n sc) :: conCases defs n ns
  conCases defs n (_ :: ns) = conCases defs n ns

  constCases : Defs -> Name -> List (CaseAlt vars) -> List (CConstAlt vars)
  constCases defs n [] = []
  constCases defs n (ConstCase x sc :: ns)
      = MkConstAlt x (toCExpTree defs n sc) :: constCases defs n ns
  constCases defs n (_ :: ns) = constCases defs n ns

  getDef : Defs -> Name -> List (CaseAlt vars) -> Maybe (CExp vars)
  getDef defs n [] = Nothing
  getDef defs n (DefaultCase sc :: ns) = Just (toCExpTree defs n sc)
  getDef defs n (_ :: ns) = getDef defs n ns

  -- Turn a case analysis on a Delay into an application of Force. We let
  -- bind the arguments, which will be inlined later. There's no point in
  -- doing anything more fiddly now!
  forceIn : Defs -> Name -> CExp vars -> (cargs : List Name) ->
            CExp (cargs ++ vars) -> CExp vars
  forceIn defs n exp [] tree = tree
  forceIn defs n exp [dexp] tree = CLet dexp (CForce exp) tree
  forceIn defs n exp (d :: ds) tree 
      = forceIn defs n exp ds (CLet d CErased tree)

  toCExpTree : Defs -> Name -> CaseTree vars -> CExp vars
  toCExpTree defs n (Case x scTy [ConCase cn t args sc])
      = if isDelay cn defs
           then forceIn defs n (CLocal x) args (toCExpTree defs n sc)
           else CConCase (CLocal x) (conCases defs n [ConCase cn t args sc])
                         Nothing
  toCExpTree defs n (Case x scTy alts@(ConCase _ _ _ _ :: _)) 
      = CConCase (CLocal x) (conCases defs n alts) (getDef defs n alts)
  toCExpTree defs n (Case x scTy alts@(ConstCase _ _ :: _)) 
      = CConstCase (CLocal x) (constCases defs n alts) (getDef defs n alts)
  toCExpTree defs n (Case x scTy alts@(DefaultCase sc :: _)) 
      = toCExpTree defs n sc
  toCExpTree defs n (Case x scTy []) = CCrash $ "Missing case tree in " ++ show n
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
toCDef n (PMDef _ args _ tree _)
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
toCDef n (DCon tag arity _)
    = pure $ MkCon tag arity
toCDef n (TCon tag arity _ _ _)
    = pure $ MkCon tag arity
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
compileExp : {auto c : Ref Ctxt Defs} -> ClosedTerm -> Core annot (CExp [])
compileExp tm
    = do defs <- get Ctxt
         pure (toCExp defs (UN "main") tm)

export
compileDef : {auto c : Ref Ctxt Defs} -> Name -> Core annot ()
compileDef n
    = do defs <- get Ctxt
         case lookupDefExact n (gamma defs) of
              Just d => do ce <- toCDef n d
                           setCompiled n ce
              Nothing => throw (InternalError ("Trying to compile unknown name " ++ show n))
