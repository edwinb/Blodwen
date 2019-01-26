module Compiler.CompileExpr

import Core.CaseTree
import public Core.CompileExpr
import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.CMap
import Data.Vect

%default covering

-- Calculate tags for type constructors from all of the modules - they need
-- to be globally unique so we don't do this until just before compilation,
-- which is when we know how many we have
public export
NameTags : Type
NameTags = SortedMap Int

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

-- Rewrite applications of Nat constructors and functions to more optimal
-- versions using Integer

-- None of these should be hard coded, but we'll do it this way until we
-- have a more general approach to optimising data types!
natHack : CExp vars -> CExp vars
natHack (CCon (NS ["Prelude"] (UN "Z")) _ []) = CPrimVal (BI 0)
natHack (CCon (NS ["Prelude"] (UN "S")) _ [k])
    = CApp (CRef (UN "prim__add_Integer")) [CPrimVal (BI 1), k]
natHack (CApp (CRef (NS ["Prelude"] (UN "natToInteger"))) [k]) = k
natHack (CApp (CRef (NS ["Prelude"] (UN "integerToNat"))) [k]) = k
natHack (CApp (CRef (NS ["Prelude"] (UN "plus"))) args)
    = CApp (CRef (UN "prim__add_Integer")) args
natHack (CApp (CRef (NS ["Prelude"] (UN "mult"))) args)
    = CApp (CRef (UN "prim__mul_Integer")) args
natHack (CApp (CRef (NS ["Nat", "Data"] (UN "minus"))) args)
    = CApp (CRef (UN "prim__sub_Integer")) args
natHack t = t

isNatCon : Name -> Bool
isNatCon (NS ["Prelude"] (UN "Z")) = True
isNatCon (NS ["Prelude"] (UN "S")) = True
isNatCon _ = False

natBranch : CConAlt vars -> Bool
natBranch (MkConAlt n _ _ _) = isNatCon n

trySBranch : CExp vars -> CConAlt vars -> Maybe (CExp vars)
trySBranch n (MkConAlt (NS ["Prelude"] (UN "S")) _ [arg] sc)
    = Just (CLet arg (CApp (CRef (UN "prim__sub_Integer")) [n, CPrimVal (BI 1)]) 
                 sc)
trySBranch _ _ = Nothing

tryZBranch : CConAlt vars -> Maybe (CExp vars)
tryZBranch (MkConAlt (NS ["Prelude"] (UN "Z")) _ [] sc) = Just sc
tryZBranch _ = Nothing

getSBranch : CExp vars -> List (CConAlt vars) -> Maybe (CExp vars)
getSBranch n [] = Nothing
getSBranch n (x :: xs) = trySBranch n x <+> getSBranch n xs

getZBranch : List (CConAlt vars) -> Maybe (CExp vars)
getZBranch [] = Nothing
getZBranch (x :: xs) = tryZBranch x <+> getZBranch xs

-- Rewrite case trees on Nat to be case trees on Integer
natHackTree : CExp vars -> CExp vars
natHackTree (CConCase sc alts def)
   = if any natBranch alts
        then let def' = maybe def Just (getSBranch sc alts) in
                 case getZBranch alts of
                      Nothing => maybe (CCrash "No branches") id def'
                      Just zalt => CConstCase sc [MkConstAlt (BI 0) zalt] def'
        else CConCase sc alts def
natHackTree t = t

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
  toCExpTm : Defs -> NameTags -> Name -> Term vars -> CExp vars
  toCExpTm defs tags n (Local _ prf) = CLocal prf
  toCExpTm defs tags n (Ref (DataCon tag arity) fn) 
      = let tag' = case lookup fn tags of
                        Just t => t
                        _ => tag in
            CCon fn tag' []
  toCExpTm defs tags n (Ref (TyCon tag arity) fn)
      = let tag' = case lookup fn tags of
                        Just t => t
                        _ => tag in
            CCon fn tag' []
  toCExpTm defs tags n (Ref _ fn) = CApp (CRef fn) []
  toCExpTm defs tags n (Bind x (Lam _ _ _) sc)
      = CLam x (toCExp defs tags n sc)
  toCExpTm defs tags n (Bind x (Let Rig0 val _) sc)
      = CLet x CErased (toCExp defs tags n sc)
  toCExpTm defs tags n (Bind x (Let _ val _) sc)
      = CLet x (toCExp defs tags n val) (toCExp defs tags n sc)
  toCExpTm defs tags n (Bind x (Pi c e ty) sc) 
      = CCon (UN "->") 1 []
  toCExpTm defs tags n (Bind x b tm) = CErased
  -- We'd expect this to have been dealt with in toCExp, but for completeness...
  toCExpTm defs tags n (App tm arg) 
      = CApp (toCExp defs tags n tm) [toCExp defs tags n arg]
  toCExpTm defs tags n (PrimVal c) 
      = let t = constTag c in
            if t == 0
               then CPrimVal c
               else CCon (UN (show c)) t []
  toCExpTm defs tags n Erased = CErased
  toCExpTm defs tags n TType = CCon (UN "Type") 2 []

  toCExp : Defs -> NameTags -> Name -> Term vars -> CExp vars
  toCExp defs tags n tm with (unapply tm)
    toCExp defs tags n (apply f args) | ArgsList 
        = let args' = map (toCExp defs tags n) args in
              maybe (natHack 
                      (expandToArity (numArgs defs f) 
                                       (toCExpTm defs tags n f) args'))
              id
              (specialApp defs f args')

mutual
  conCases : Defs -> NameTags -> Name -> List (CaseAlt vars) -> List (CConAlt vars)
  conCases defs tags n [] = []
  conCases defs tags n (ConCase x tag args sc :: ns)
      = let tag' = case lookup x tags of
                        Just t => t
                        _ => tag in
            MkConAlt x tag' args (toCExpTree defs tags n sc) 
                 :: conCases defs tags n ns
  conCases defs tags n (_ :: ns) = conCases defs tags n ns

  constCases : Defs -> NameTags -> Name -> List (CaseAlt vars) -> List (CConstAlt vars)
  constCases defs tags n [] = []
  constCases defs tags n (ConstCase x sc :: ns)
      = MkConstAlt x (toCExpTree defs tags n sc) :: constCases defs tags n ns
  constCases defs tags n (_ :: ns) = constCases defs tags n ns

  getDef : Defs -> NameTags -> Name -> List (CaseAlt vars) -> Maybe (CExp vars)
  getDef defs tags n [] = Nothing
  getDef defs tags n (DefaultCase sc :: ns) = Just (toCExpTree defs tags n sc)
  getDef defs tags n (_ :: ns) = getDef defs tags n ns

  -- Turn a case analysis on a Delay into an application of Force. We let
  -- bind the arguments, which will be inlined later. There's no point in
  -- doing anything more fiddly now!
  forceIn : Defs -> Name -> CExp vars -> (cargs : List Name) ->
            CExp (cargs ++ vars) -> CExp vars
  forceIn defs n exp [] tree = tree
  forceIn defs n exp [dexp] tree = CLet dexp (CForce exp) tree
  forceIn defs n exp (d :: ds) tree 
      = forceIn defs n exp ds (CLet d CErased tree)

  toCExpTree : Defs -> NameTags -> Name -> CaseTree vars -> CExp vars
  toCExpTree defs tags n (Case x scTy [ConCase cn t args sc])
      = if isDelay cn defs
           then forceIn defs n (CLocal x) args (toCExpTree defs tags n sc)
           else natHackTree 
                  (CConCase (CLocal x) (conCases defs tags n [ConCase cn t args sc])
                            Nothing)
  toCExpTree defs tags n (Case x scTy alts@(ConCase _ _ _ _ :: _)) 
      = natHackTree 
           (CConCase (CLocal x) (conCases defs tags n alts) (getDef defs tags n alts))
  toCExpTree defs tags n (Case x scTy alts@(ConstCase _ _ :: _)) 
      = CConstCase (CLocal x) (constCases defs tags n alts) (getDef defs tags n alts)
  toCExpTree defs tags n (Case x scTy alts@(DefaultCase sc :: _)) 
      = toCExpTree defs tags n sc
  toCExpTree defs tags n (Case x scTy []) = CCrash $ "Missing case tree in " ++ show n
  toCExpTree defs tags n (STerm tm) = toCExp defs tags n tm
  toCExpTree defs tags n (Unmatched msg) = CCrash msg 
  toCExpTree defs tags n Impossible = CCrash $ "Impossible case encountered in " ++ show n

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

toCDef : {auto c : Ref Ctxt Defs} -> NameTags -> Name -> Def -> Core annot CDef
toCDef tags n None
    = pure $ MkError $ CCrash ("Encountered undefined name " ++ show n)
toCDef tags n (PMDef _ args _ tree _)
    = pure $ MkFun _ (toCExpTree !(get Ctxt) tags n tree) 
toCDef tags n (ExternDef arity)
    = let (ns ** args) = mkArgList 0 arity in
          pure $ MkFun _ (CExtPrim n (map toArgExp (getVars args)))
  where
    toArgExp : (x ** List.Elem x ns) -> CExp ns
    toArgExp (x ** p) = CLocal p

    getVars : ArgList k ns -> List (x ** List.Elem x ns)
    getVars NoArgs = []
    getVars (ConsArg a rest) = (a ** Here) :: map weakenEl (getVars rest)
toCDef tags n (Builtin {arity} op)
    = let (ns ** args) = mkArgList 0 arity in
          pure $ MkFun _ (COp op (map toArgExp (getVars args)))
  where
    toArgExp : (x ** List.Elem x ns) -> CExp ns
    toArgExp (x ** p) = CLocal p

    getVars : ArgList k ns -> Vect k (x ** List.Elem x ns)
    getVars NoArgs = []
    getVars (ConsArg a rest) = (a ** Here) :: map weakenEl (getVars rest)
toCDef tags n (DCon tag arity _)
    = case lookup n tags of
           Just t => pure $ MkCon t arity
           _ => pure $ MkCon tag arity
toCDef tags n (TCon tag arity _ _ _ _)
    = case lookup n tags of
           Just t => pure $ MkCon t arity
           _ => pure $ MkCon tag arity
-- We do want to be able to compile these, but also report an error at run time
-- (and, TODO: warn at compile time)
toCDef tags n (Hole _ _ _)
    = pure $ MkError $ CCrash ("Encountered unimplemented hole " ++ show n)
toCDef tags n (Guess _ _)
    = pure $ MkError $ CCrash ("Encountered constrained hole " ++ show n)
toCDef tags n (BySearch _ _)
    = pure $ MkError $ CCrash ("Encountered incomplete proof search " ++ show n)
toCDef tags n def
    = pure $ MkError $ CCrash ("Encountered uncompilable name " ++ show (n, def))

export
compileExp : {auto c : Ref Ctxt Defs} -> 
             NameTags -> ClosedTerm -> Core annot (CExp [])
compileExp tags tm
    = do defs <- get Ctxt
         pure (toCExp defs tags (UN "main") tm)

export
compileDef : {auto c : Ref Ctxt Defs} -> NameTags -> Name -> Core annot ()
compileDef tags n
    = do defs <- get Ctxt
         case lookupDefExact n (gamma defs) of
              Just d => do ce <- toCDef tags n d
                           setCompiled n ce
              Nothing => throw (InternalError ("Trying to compile unknown name " ++ show n))
