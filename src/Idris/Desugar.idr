module Idris.Desugar

import Core.Binary
import Core.Context
import Core.Core
import Core.Options
import Core.TT
import Core.Unify

import Data.StringMap

import Idris.BindImplicits
import Idris.Syntax

import Idris.Elab.Implementation
import Idris.Elab.Interface

import Parser.RawImp

import TTImp.TTImp
import TTImp.Utils

import Utils.Shunting

import Control.Monad.State

-- Convert high level Idris declarations (PDecl from Idris.Syntax) into
-- TTImp, recording any high level syntax info on the way (e.g. infix
-- operators)

-- Desugaring from high level Idris syntax to TTImp involves:

-- Done:
-- * Shunting infix operators into function applications according to precedence
-- * Replacing 'do' notating with applications of (>>=)
-- * Replacing pattern matching binds with 'case'
-- * Changing tuples to 'Pair/MkPair'
-- * List notation

-- Still TODO:
-- * Replacing !-notation
-- * Dependent pair notation
-- * Idiom brackets

%default covering

public export
data Side = LHS | AnyExpr

export
extendAs : {auto s : Ref Syn SyntaxInfo} ->
         List String -> List String -> SyntaxInfo -> Core annot ()
extendAs old as newsyn
    = do syn <- get Syn
         put Syn (record { infixes $= mergeLeft (infixes newsyn),
                           prefixes $= mergeLeft (prefixes newsyn),
                           ifaces $= mergeContextAs old as (ifaces newsyn) } 
                  syn)

mkPrec : Fixity -> Nat -> OpPrec
mkPrec InfixL p = AssocL p
mkPrec InfixR p = AssocR p
mkPrec Infix p = NonAssoc p
mkPrec Prefix p = Prefix p

toTokList : {auto s : Ref Syn SyntaxInfo} ->
            PTerm -> Core FC (List (Tok FC PTerm))
toTokList (POp fc op l r)
    = do syn <- get Syn
         case lookup op (infixes syn) of
              Nothing => throw (GenericMsg fc $ "Unknown operator '" ++ op ++ "'")
              Just (Prefix, _) =>
                      throw (GenericMsg fc $ "'" ++ op ++ "' is a prefix operator")
              Just (fix, prec) =>
                   do rtoks <- toTokList r
                      pure (Expr l :: Op fc op (mkPrec fix prec) :: rtoks)
toTokList (PPrefixOp fc op arg)
    = do syn <- get Syn
         case lookup op (prefixes syn) of
              Nothing =>
                   throw (GenericMsg fc $ "'" ++ op ++ "' is not a prefix operator")
              Just prec =>
                   do rtoks <- toTokList arg
                      pure (Op fc op (Prefix prec) :: rtoks)
toTokList t = pure [Expr t]

mutual
  export
  desugar : {auto s : Ref Syn SyntaxInfo} ->
            {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST (UState FC)} ->
            {auto i : Ref ImpST (ImpState FC)} ->
            Side -> List Name -> PTerm -> Core FC (RawImp FC)
  desugar side ps (PRef fc x) = pure $ IVar fc x
  desugar side ps (PPi fc rig p mn argTy retTy) 
      = let ps' = maybe ps (:: ps) mn in
            pure $ IPi fc rig p mn !(desugar side ps argTy) 
                                   !(desugar side ps' retTy)
  desugar side ps (PLam fc rig p n argTy scope) 
      = pure $ ILam fc rig p (Just n) !(desugar side ps argTy) 
                                      !(desugar side (n :: ps) scope)
  desugar side ps (PLet fc rig (PRef _ n) nTy nVal scope [])
      = pure $ ILet fc rig n !(desugar side ps nTy) !(desugar side ps nVal) 
                             !(desugar side (n :: ps) scope)
  desugar side ps (PLet fc rig pat nTy nVal scope alts) 
      = pure $ ICase fc !(desugar side ps nVal) !(desugar side ps nTy)
                        !(traverse (desugarClause ps True) 
                            (MkPatClause fc pat scope [] :: alts))
  desugar side ps (PCase fc x xs) 
      = pure $ ICase fc !(desugar side ps x) 
                        (Implicit fc)
                        !(traverse (desugarClause ps True) xs)
  desugar side ps (PLocal fc xs scope) 
      = pure $ ILocal fc (concat !(traverse (desugarDecl ps) xs)) 
                         !(desugar side (definedIn xs ++ ps) scope)
  desugar side ps (PApp fc x y) 
      = pure $ IApp fc !(desugar side ps x) !(desugar side ps y)
  desugar side ps (PImplicitApp fc x argn y) 
      = pure $ IImplicitApp fc !(desugar side ps x) argn !(desugar side ps y)
  desugar side ps (PEq fc l r)
      = do l' <- desugar side ps l
           r' <- desugar side ps r
           pure $ apply (IVar fc (UN "Equal")) [l', r']
  desugar side ps (PBracketed fc e) = desugar side ps e
  desugar side ps (POp fc op l r) 
      = do ts <- toTokList (POp fc op l r)
           desugarTree side ps !(parseOps ts)
  desugar side ps (PPrefixOp fc op arg) 
      = do ts <- toTokList (PPrefixOp fc op arg)
           desugarTree side ps !(parseOps ts)
  desugar side ps (PSectionL fc op arg) 
      = do syn <- get Syn
           -- It might actually be a prefix argument rather than a section
           -- so check that first, otherwise desugar as a lambda
           case lookup op (prefixes syn) of
                Nothing => 
                   desugar side ps (PLam fc RigW Explicit (MN "arg" 0) (PImplicit fc)
                               (POp fc op (PRef fc (MN "arg" 0)) arg))
                Just prec => desugar side ps (PPrefixOp fc op arg)
  desugar side ps (PSectionR fc arg op)
      = desugar side ps (PLam fc RigW Explicit (MN "arg" 0) (PImplicit fc)
                 (POp fc op arg (PRef fc (MN "arg" 0))))
  desugar side ps (PSearch fc depth) = pure $ ISearch fc depth
  desugar side ps (PPrimVal fc (BI x))
      = do defs <- get Ctxt
           case fromIntegerName defs of
                Nothing =>
                   pure $ IAlternative fc (UniqueDefault (IPrimVal fc (BI x)))
                                   [IPrimVal fc (BI x),
                                    IPrimVal fc (I (fromInteger x))]
                Just fi => pure $ IApp fc (IVar fc fi) 
                                          (IPrimVal fc (BI x))
  desugar side ps (PPrimVal fc (Str x))
      = do defs <- get Ctxt
           case fromStringName defs of
                Nothing =>
                   pure $ IPrimVal fc (Str x)
                Just f => pure $ IApp fc (IVar fc f) 
                                         (IPrimVal fc (Str x))
  desugar side ps (PPrimVal fc (Ch x))
      = do defs <- get Ctxt
           case fromCharName defs of
                Nothing =>
                   pure $ IPrimVal fc (Ch x)
                Just f => pure $ IApp fc (IVar fc f) 
                                         (IPrimVal fc (Ch x))
  desugar side ps (PPrimVal fc x) = pure $ IPrimVal fc x
  desugar side ps (PQuote fc x) = pure $ IQuote fc !(desugar side ps x)
  desugar side ps (PUnquote fc x) = pure $ IUnquote fc !(desugar side ps x)
  desugar side ps (PHole fc holename) = pure $ IHole fc holename
  desugar side ps (PType fc) = pure $ IType fc
  desugar side ps (PAs fc vname pattern) 
      = pure $ IAs fc vname !(desugar side ps pattern)
  desugar side ps (PDotted fc x) 
      = pure $ IMustUnify fc "User dotted" !(desugar side ps x)
  desugar side ps (PImplicit fc) = pure $ Implicit fc
  desugar side ps (PInfer fc) = pure $ Infer fc
  desugar side ps (PDoBlock fc block)
      = expandDo side ps fc block
  desugar side ps (PList fc args)
      = expandList side ps fc args
  desugar side ps (PPair fc l r) 
      = do l' <- desugar side ps l
           r' <- desugar side ps r
           let pval = apply (IVar fc (UN "MkPair")) [l', r']
           pure $ IAlternative fc (UniqueDefault pval)
                  [apply (IVar fc (UN "Pair")) [l', r'], pval]
  desugar side ps (PUnit fc) 
      = pure $ IAlternative fc (UniqueDefault (IVar fc (UN "MkUnit")))
               [IVar fc (UN "Unit"), 
                IVar fc (UN "MkUnit")]
  desugar side ps (PIfThenElse fc x t e)
      = pure $ ICase fc !(desugar side ps x) (Implicit fc)
                   [PatClause fc (IVar fc (UN "True")) !(desugar side ps t),
                    PatClause fc (IVar fc (UN "False")) !(desugar side ps e)]
  desugar side ps (PComprehension fc ret conds)
      = desugar side ps (PDoBlock fc (map guard conds ++ [toPure ret]))
    where
      guard : PDo -> PDo
      guard (DoExp fc tm) = DoExp fc (PApp fc (PRef fc (UN "guard")) tm)
      guard d = d

      toPure : PTerm -> PDo
      toPure tm = DoExp fc (PApp fc (PRef fc (UN "pure")) tm)
  desugar side ps (PRewrite fc rule tm)
      = pure $ IRewrite fc !(desugar side ps rule) !(desugar side ps tm)

  expandList : {auto s : Ref Syn SyntaxInfo} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState FC)} ->
               {auto i : Ref ImpST (ImpState FC)} ->
               Side -> List Name -> FC -> List PTerm -> Core FC (RawImp FC)
  expandList side ps fc [] = pure (IVar fc (UN "Nil"))
  expandList side ps fc (x :: xs)
      = pure $ apply (IVar fc (UN "::")) 
                [!(desugar side ps x), !(expandList side ps fc xs)]

  expandDo : {auto s : Ref Syn SyntaxInfo} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState FC)} ->
             {auto i : Ref ImpST (ImpState FC)} ->
             Side -> List Name -> FC -> List PDo -> Core FC (RawImp FC)
  expandDo side ps fc [] = throw (GenericMsg fc "Do block cannot be empty")
  expandDo side ps _ [DoExp fc tm] = desugar side ps tm
  expandDo side ps fc [e] 
      = throw (GenericMsg (getLoc e) 
                  "Last statement in do block must be an expression") 
  expandDo side ps topfc (DoExp fc tm :: rest)
      = do tm' <- desugar side ps tm
           rest' <- expandDo side ps topfc rest
           gam <- get Ctxt
           -- If 'const' exists, use it, to reduce the size of the environment
           -- (this avoids it making a mess in displays, needlessly extending
           -- the environment for searches, etc)
           case lookupTyName (UN "const") (gamma gam) of
                [] => pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) tm')
                                  (ILam fc RigW Explicit Nothing (Implicit fc) rest')
                _ => pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) tm')
                                 (IApp fc (IVar fc (UN "const")) rest')
  expandDo side ps topfc (DoBind fc n tm :: rest)
      = do tm' <- desugar side ps tm
           rest' <- expandDo side ps topfc rest
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) tm')
                     (ILam fc RigW Explicit (Just n) (Implicit fc) rest')
  expandDo side ps topfc (DoBindPat fc pat exp alts :: rest)
      = do pat' <- desugar LHS ps pat
           let (newps, bpat) = bindNames False pat'
           exp' <- desugar side ps exp
           alts' <- traverse (desugarClause ps True) alts
           let ps' = newps ++ ps
           rest' <- expandDo side ps' topfc rest
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) exp')
                    (ILam fc RigW Explicit (Just (MN "_" 0)) (Implicit fc)
                          (ICase fc (IVar fc (MN "_" 0))
                               (Implicit fc)
                               (PatClause fc bpat rest' 
                                  :: alts')))
  expandDo side ps topfc (DoLet fc n rig tm :: rest) 
      = do tm' <- desugar side ps tm
           rest' <- expandDo side ps topfc rest
           pure $ ILet fc rig n (Implicit fc) tm' rest'
  expandDo side ps topfc (DoLetPat fc pat tm alts :: rest) 
      = do pat' <- desugar LHS ps pat
           let (newps, bpat) = bindNames False pat'
           tm' <- desugar side ps tm
           alts' <- traverse (desugarClause ps True) alts
           let ps' = newps ++ ps
           rest' <- expandDo side ps' topfc rest
           pure $ ICase fc tm' (Implicit fc) 
                       (PatClause fc bpat rest'
                                  :: alts')
  expandDo side ps topfc (DoLetLocal fc decls :: rest)
      = do rest' <- expandDo side ps topfc rest
           decls' <- traverse (desugarDecl ps) decls
           pure $ ILocal fc (concat decls') rest'
  expandDo side ps topfc (DoRewrite fc rule :: rest)
      = do rest' <- expandDo side ps topfc rest
           rule' <- desugar side ps rule
           pure $ IRewrite fc rule' rest'

  desugarTree : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                {auto i : Ref ImpST (ImpState FC)} ->
                Side -> List Name -> Tree FC PTerm -> Core FC (RawImp FC)
  desugarTree side ps (Inf loc "=" l r) -- special case since '=' is special syntax
      = do l' <- desugarTree side ps l
           r' <- desugarTree side ps r
           pure (IApp loc (IApp loc (IVar loc (UN "Equal")) l') r')
  desugarTree side ps (Inf loc op l r)
      = do l' <- desugarTree side ps l
           r' <- desugarTree side ps r
           pure (IApp loc (IApp loc (IVar loc (UN op)) l') r')
  -- negation is a special case, since we can't have an operator with
  -- two meanings otherwise
  desugarTree side ps (Pre loc "-" arg)
      = do arg' <- desugarTree side ps arg
           pure (IApp loc (IVar loc (UN "negate")) arg')
  desugarTree side ps (Pre loc op arg)
      = do arg' <- desugarTree side ps arg
           pure (IApp loc (IVar loc (UN op)) arg')
  desugarTree side ps (Leaf t) = desugar side ps t

  desugarType : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                {auto i : Ref ImpST (ImpState FC)} ->
                List Name -> PTypeDecl -> Core FC (ImpTy FC)
  desugarType ps (MkPTy fc n ty) 
      = pure $ MkImpTy fc n (bindTypeNames ps !(desugar AnyExpr ps ty))

  desugarClause : {auto s : Ref Syn SyntaxInfo} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST (UState FC)} ->
                  {auto i : Ref ImpST (ImpState FC)} ->
                  List Name -> Bool -> PClause -> Core FC (ImpClause FC)
  desugarClause ps arg (MkPatClause fc lhs rhs wheres)
      = do ws <- traverse (desugarDecl ps) wheres
           let (bound, blhs) = bindNames arg !(desugar LHS ps lhs)
           rhs' <- desugar AnyExpr (bound ++ ps) rhs
           pure $ PatClause fc blhs 
                     (case ws of
                           [] => rhs'
                           _ => ILocal fc (concat ws) rhs')
  desugarClause ps arg (MkImpossible fc lhs)
      = do dlhs <- desugar LHS ps lhs
           pure $ ImpossibleClause fc (snd (bindNames arg dlhs))

  desugarData : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                {auto i : Ref ImpST (ImpState FC)} ->
                List Name -> PDataDecl -> Core FC (ImpData FC)
  desugarData ps (MkPData fc n tycon opts datacons) 
      = pure $ MkImpData fc n (bindTypeNames ps !(desugar AnyExpr ps tycon))
                              opts
                              !(traverse (desugarType ps) datacons)
  desugarData ps (MkPLater fc n tycon) 
      = pure $ MkImpLater fc n (bindTypeNames ps !(desugar AnyExpr ps tycon))

  -- Given a high level declaration, return a list of TTImp declarations
  -- which process it, and update any necessary state on the way.
  export
  desugarDecl : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                {auto i : Ref ImpST (ImpState FC)} ->
                List Name -> PDecl -> Core FC (List (ImpDecl FC))
  desugarDecl ps (PClaim fc vis opts ty) 
      = pure [IClaim fc vis opts !(desugarType ps ty)]
  desugarDecl ps (PDef fc clauses) 
  -- The clauses won't necessarily all be from the same function, so split
  -- after desugaring, by function name, using collectDefs from RawImp
      = do cs <- traverse (desugarClause ps False) clauses
           defs <- traverse toIDef cs
           pure (collectDefs defs) 
    where
      getFn : RawImp FC -> Core FC Name
      getFn (IVar _ n) = pure n
      getFn (IApp _ f a) = getFn f
      getFn (IImplicitApp _ f _ a) = getFn f
      getFn tm = throw (InternalError (show tm ++ " is not a function application"))

      toIDef : ImpClause FC -> Core FC (ImpDecl FC)
      toIDef (PatClause fc lhs rhs) 
          = pure $ IDef fc !(getFn lhs) [PatClause fc lhs rhs]
      toIDef (ImpossibleClause fc lhs) 
          = pure $ IDef fc !(getFn lhs) [ImpossibleClause fc lhs]

  desugarDecl ps (PData fc vis ddecl) 
      = pure [IData fc vis !(desugarData ps ddecl)]
  desugarDecl ps (PReflect fc tm)
      = pure [IReflect fc !(desugar AnyExpr ps tm)]
  desugarDecl ps (PInterface fc vis cons tn params det conname body)
      = do cons' <- traverse (\ ntm => do tm' <- desugar AnyExpr (ps ++ map fst params)
                                                         (snd ntm)
                                          pure (fst ntm, tm')) cons
           params' <- traverse (\ ntm => do tm' <- desugar AnyExpr ps (snd ntm)
                                            pure (fst ntm, tm')) params
           -- Look for bindable names in all the constraints and parameters
           let bnames = concatMap (findBindableNames True (ps ++ map fst params) []) (map snd cons') ++
                        concatMap (findBindableNames True (ps ++ map fst params) []) (map snd params')
           let paramsb = map (\ (n, tm) => (n, doBind bnames tm)) params'
           let consb = map (\ (n, tm) => (n, doBind bnames tm)) cons'

           body' <- traverse (desugarDecl (ps ++ map fst params)) body
           pure [IPragma (\env, nest => 
                             elabInterface fc vis env nest consb
                                           tn paramsb det conname 
                                           (concat body'))]
  desugarDecl ps (PImplementation fc vis cons tn params impname body)
      = do cons' <- traverse (\ ntm => do tm' <- desugar AnyExpr ps (snd ntm)
                                          pure (fst ntm, tm')) cons
           params' <- traverse (desugar AnyExpr ps) params
           -- Look for bindable names in all the constraints and parameters
           let bnames = concatMap (findBindableNames True ps []) (map snd cons') ++
                        concatMap (findBindableNames True ps []) params'
           let paramsb = map (doBind bnames) params'
           let consb = map (\ (n, tm) => (n, doBind bnames tm)) cons'

           body' <- maybe (pure Nothing)
                          (\b => do b' <- traverse (desugarDecl ps) b
                                    pure (Just (concat b'))) body
           pure [IPragma (\env, nest =>
                             elabImplementation fc vis env nest consb
                                                tn paramsb impname 
                                                body')]
  desugarDecl ps (PFixity fc Prefix prec n) 
      = do syn <- get Syn
           put Syn (record { prefixes $= insert n prec } syn)
           pure []
  desugarDecl ps (PFixity fc fix prec n) 
      = do syn <- get Syn
           put Syn (record { infixes $= insert n (fix, prec) } syn)
           pure []
  desugarDecl ps (PNamespace fc ns decls)
      = do ds <- traverse (desugarDecl ps) decls
           pure [INamespace fc ns (concat ds)]
  desugarDecl ps (PDirective fc d) 
      = case d of
             Hide e n => pure [IPragma (\env, nest => hide fc e n)]
             Logging i => pure [ILog i]
             LazyNames ty d f => pure [IPragma (\env, nest => setLazy fc ty d f)]
             LazyOn a => pure [IPragma (\env, nest => lazyActive a)]
             PairNames ty f s => pure [IPragma (\env, nest => setPair fc ty f s)]
             RewriteName eq rw => pure [IPragma (\env, next => setRewrite fc eq rw)]
             PrimInteger n => pure [IPragma (\env, next => setFromInteger fc n)]
             PrimString n => pure [IPragma (\env, next => setFromString fc n)]
             PrimChar n => pure [IPragma (\env, next => setFromChar fc n)]
             CGAction cg dir => pure [IPragma (\env, nest => addDirective cg dir)]
             StartExpr tm => pure [IPragma (\env, nest => throw (InternalError "%start not implemented"))] -- TODO!

