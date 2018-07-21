module Idris.Desugar

import Core.Binary
import Core.Context
import Core.Core
import Core.TT
import Core.Unify

import Data.StringMap

import Utils.Shunting

import Idris.BindImplicits
import Idris.Syntax

import Idris.Elab.Implementation
import Idris.Elab.Interface

import TTImp.TTImp

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

export
extendAs : {auto s : Ref Syn SyntaxInfo} ->
         List String -> List String -> SyntaxInfo -> Core annot ()
extendAs old as newsyn
    = do syn <- get Syn
         put Syn (record { infixes $= mergeLeft (infixes newsyn),
                           prefixes $= mergeLeft (prefixes newsyn),
                           ifaces $= mergeContextAs old as (ifaces newsyn) } 
                  syn)

-- Add 'IMustUnify' for any duplicated names, and any function application
addDots : RawImp annot -> RawImp annot
addDots tm = tm

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
            List Name -> PTerm -> Core FC (RawImp FC)
  desugar ps (PRef fc x) = pure $ IVar fc x
  desugar ps (PPi fc rig p mn argTy retTy) 
      = let ps' = maybe ps (:: ps) mn in
            pure $ IPi fc rig p mn !(desugar ps argTy) 
                                   !(desugar ps' retTy)
  desugar ps (PLam fc rig p n argTy scope) 
      = pure $ ILam fc rig p n !(desugar ps argTy) 
                               !(desugar (n :: ps) scope)
  desugar ps (PLet fc rig (PRef _ n) nTy nVal scope [])
      = pure $ ILet fc rig n !(desugar ps nTy) !(desugar ps nVal) 
                             !(desugar (n :: ps) scope)
  desugar ps (PLet fc rig pat nTy nVal scope alts) 
      = pure $ ICase fc !(desugar ps nVal) !(desugar ps nTy)
                        !(traverse (desugarClause ps True) 
                            (MkPatClause fc pat scope [] :: alts))
  desugar ps (PCase fc x xs) 
      = pure $ ICase fc !(desugar ps x) 
                        (Implicit fc)
                        !(traverse (desugarClause ps True) xs)
  desugar ps (PLocal fc xs scope) 
      = pure $ ILocal fc (concat !(traverse (desugarDecl ps) xs)) 
                         !(desugar (definedIn xs ++ ps) scope)
  desugar ps (PApp fc x y) 
      = pure $ IApp fc !(desugar ps x) !(desugar ps y)
  desugar ps (PImplicitApp fc x argn y) 
      = pure $ IImplicitApp fc !(desugar ps x) argn !(desugar ps y)
  desugar ps (PEq fc l r)
      = do l' <- desugar ps l
           r' <- desugar ps r
           pure $ apply (IVar fc (UN "Equal")) [l', r']
  desugar ps (PBracketed fc e) = desugar ps e
  desugar ps (POp fc op l r) 
      = do ts <- toTokList (POp fc op l r)
           desugarTree ps !(parseOps ts)
  desugar ps (PPrefixOp fc op arg) 
      = do ts <- toTokList (PPrefixOp fc op arg)
           desugarTree ps !(parseOps ts)
  desugar ps (PSectionL fc op arg) 
      = do syn <- get Syn
           -- It might actually be a prefix argument rather than a section
           -- so check that first, otherwise desugar as a lambda
           case lookup op (prefixes syn) of
                Nothing => 
                   desugar ps (PLam fc RigW Explicit (MN "arg" 0) (PImplicit fc)
                               (POp fc op (PRef fc (MN "arg" 0)) arg))
                Just prec => desugar ps (PPrefixOp fc op arg)
  desugar ps (PSectionR fc arg op)
      = desugar ps (PLam fc RigW Explicit (MN "arg" 0) (PImplicit fc)
                 (POp fc op arg (PRef fc (MN "arg" 0))))
  desugar ps (PSearch fc depth) = pure $ ISearch fc depth
  desugar ps (PPrimVal fc (BI x))
      = pure $ IAlternative fc (UniqueDefault (IPrimVal fc (BI x)))
                               [IPrimVal fc (BI x), 
                                IPrimVal fc (I (fromInteger x))]
  desugar ps (PPrimVal fc x) = pure $ IPrimVal fc x
  desugar ps (PQuote fc x) = pure $ IQuote fc !(desugar ps x)
  desugar ps (PUnquote fc x) = pure $ IUnquote fc !(desugar ps x)
  desugar ps (PHole fc holename) = pure $ IHole fc holename
  desugar ps (PType fc) = pure $ IType fc
  desugar ps (PAs fc vname pattern) 
      = pure $ IAs fc vname !(desugar ps pattern)
  desugar ps (PDotted fc x) 
      = pure $ IMustUnify fc !(desugar ps x)
  desugar ps (PImplicit fc) = pure $ Implicit fc
  desugar ps (PDoBlock fc block)
      = expandDo ps fc block
  desugar ps (PList fc args)
      = expandList ps fc args
  desugar ps (PPair fc l r) 
      = do l' <- desugar ps l
           r' <- desugar ps r
           pure $ IAlternative fc Unique
                  [apply (IVar fc (UN "Pair")) [l', r'],
                   apply (IVar fc (UN "MkPair")) [l', r']]
  desugar ps (PUnit fc) 
      = pure $ IAlternative fc Unique 
               [IVar fc (UN "Unit"), 
                IVar fc (UN "MkUnit")]
  desugar ps (PIfThenElse fc x t e)
      = pure $ ICase fc !(desugar ps x) (Implicit fc)
                   [PatClause fc (IVar fc (UN "True")) !(desugar ps t),
                    PatClause fc (IVar fc (UN "False")) !(desugar ps e)]
  
  expandList : {auto s : Ref Syn SyntaxInfo} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState FC)} ->
               {auto i : Ref ImpST (ImpState FC)} ->
               List Name -> FC -> List PTerm -> Core FC (RawImp FC)
  expandList ps fc [] = pure (IVar fc (UN "Nil"))
  expandList ps fc (x :: xs)
      = pure $ apply (IVar fc (UN "::")) [!(desugar ps x), !(expandList ps fc xs)]

  expandDo : {auto s : Ref Syn SyntaxInfo} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState FC)} ->
             {auto i : Ref ImpST (ImpState FC)} ->
             List Name -> FC -> List PDo -> Core FC (RawImp FC)
  expandDo ps fc [] = throw (GenericMsg fc "Do block cannot be empty")
  expandDo ps _ [DoExp fc tm] = desugar ps tm
  expandDo ps fc [e] 
      = throw (GenericMsg (getLoc e) 
                  "Last statement in do block must be an expression") 
  expandDo ps topfc (DoExp fc tm :: rest)
      = do tm' <- desugar ps tm
           rest' <- expandDo ps topfc rest
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) tm')
                     (ILam fc RigW Explicit (UN "_") (Implicit fc) rest')
  expandDo ps topfc (DoBind fc n tm :: rest)
      = do tm' <- desugar ps tm
           rest' <- expandDo ps topfc rest
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) tm')
                     (ILam fc RigW Explicit n (Implicit fc) rest')
  expandDo ps topfc (DoBindPat fc pat exp alts :: rest)
      = do pat' <- desugar ps pat
           let (newps, bpat) = bindNames False pat'
           exp' <- desugar ps exp
           alts' <- traverse (desugarClause ps True) alts
           let ps' = newps ++ ps
           rest' <- expandDo ps' topfc rest
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) exp')
                    (ILam fc RigW Explicit (MN "_" 0) (Implicit fc)
                          (ICase fc (IVar fc (MN "_" 0))
                               (Implicit fc)
                               (PatClause fc bpat rest' 
                                  :: alts')))
  expandDo ps topfc (DoLet fc n rig tm :: rest) 
      = do tm' <- desugar ps tm
           rest' <- expandDo ps topfc rest
           pure $ ILet fc rig n (Implicit fc) tm' rest'
  expandDo ps topfc (DoLetPat fc pat tm alts :: rest) 
      = do pat' <- desugar ps pat
           let (newps, bpat) = bindNames False pat'
           tm' <- desugar ps tm
           alts' <- traverse (desugarClause ps True) alts
           let ps' = newps ++ ps
           rest' <- expandDo ps' topfc rest
           pure $ ICase fc tm' (Implicit fc) 
                       (PatClause fc bpat rest'
                                  :: alts')
  expandDo ps topfc (DoLetLocal fc decls :: rest)
      = do rest' <- expandDo ps topfc rest
           decls' <- traverse (desugarDecl ps) decls
           pure $ ILocal fc (concat decls') rest'

  desugarTree : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                {auto i : Ref ImpST (ImpState FC)} ->
                List Name -> Tree FC PTerm -> Core FC (RawImp FC)
  desugarTree ps (Inf loc op l r)
      = do l' <- desugarTree ps l
           r' <- desugarTree ps r
           pure (IApp loc (IApp loc (IVar loc (UN op)) l') r')
  desugarTree ps (Pre loc op arg)
      = do arg' <- desugarTree ps arg
           pure (IApp loc (IVar loc (UN op)) arg')
  desugarTree ps (Leaf t) = desugar ps t

  desugarType : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                {auto i : Ref ImpST (ImpState FC)} ->
                List Name -> PTypeDecl -> Core FC (ImpTy FC)
  desugarType ps (MkPTy fc n ty) 
      = pure $ MkImpTy fc n (bindTypeNames ps !(desugar ps ty))

  desugarClause : {auto s : Ref Syn SyntaxInfo} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST (UState FC)} ->
                  {auto i : Ref ImpST (ImpState FC)} ->
                  List Name -> Bool -> PClause -> Core FC (ImpClause FC)
  desugarClause ps arg (MkPatClause fc lhs rhs wheres)
      = do ws <- traverse (desugarDecl ps) wheres
           let (bound, blhs) = bindNames arg !(desugar ps lhs)
           rhs' <- desugar (bound ++ ps) rhs
           pure $ PatClause fc blhs 
                     (case ws of
                           [] => rhs'
                           _ => ILocal fc (concat ws) rhs')
  desugarClause ps arg (MkImpossible fc lhs) 
      = pure $ ImpossibleClause fc (snd (bindNames arg !(desugar ps lhs)))

  desugarData : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                {auto i : Ref ImpST (ImpState FC)} ->
                List Name -> PDataDecl -> Core FC (ImpData FC)
  desugarData ps (MkPData fc n tycon opts datacons) 
      = pure $ MkImpData fc n (bindTypeNames ps !(desugar ps tycon))
                              opts
                              !(traverse (desugarType ps) datacons)
  desugarData ps (MkPLater fc n tycon) 
      = pure $ MkImpLater fc n (bindTypeNames ps !(desugar ps tycon))

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
  desugarDecl ps (PDef fc n clauses) 
      = pure [IDef fc n !(traverse (desugarClause ps False) clauses)]
  desugarDecl ps (PData fc vis ddecl) 
      = pure [IData fc vis !(desugarData ps ddecl)]
  desugarDecl ps (PReflect fc tm)
      = pure [IReflect fc !(desugar ps tm)]
  desugarDecl ps (PInterface fc vis cons tn params det conname body)
      = do cons' <- traverse (\ ntm => do tm' <- desugar ps (snd ntm)
                                          pure (fst ntm, tm')) cons
           params' <- traverse (\ ntm => do tm' <- desugar ps (snd ntm)
                                            pure (fst ntm, tm')) params
           -- Look for bindable names in all the constraints and parameters
           let bnames = concatMap (findBindableNames True ps []) (map snd cons') ++
                        concatMap (findBindableNames True ps []) (map snd params')
           let paramsb = map (\ (n, tm) => (n, doBind bnames tm)) params'
           let consb = map (\ (n, tm) => (n, doBind bnames tm)) cons'

           body' <- traverse (desugarDecl (ps ++ map fst params)) body
           pure [IPragma (\env, nest => 
                             elabInterface fc vis env nest consb
                                           tn paramsb det conname 
                                           (concat body'))]
  desugarDecl ps (PImplementation fc vis cons tn params impname body)
      = do cons' <- traverse (\ ntm => do tm' <- desugar ps (snd ntm)
                                          pure (fst ntm, tm')) cons
           params' <- traverse (desugar ps) params
           -- Look for bindable names in all the constraints and parameters
           let bnames = concatMap (findBindableNames True ps []) (map snd cons') ++
                        concatMap (findBindableNames True ps []) params'
           let paramsb = map (doBind bnames) params'
           let consb = map (\ (n, tm) => (n, doBind bnames tm)) cons'

           body' <- traverse (desugarDecl ps) body
           pure [IPragma (\env, nest =>
                             elabImplementation fc vis env nest consb
                                                tn paramsb impname 
                                                (concat body'))]
  desugarDecl ps (PFixity fc Prefix prec n) 
      = do syn <- get Syn
           put Syn (record { prefixes $= insert n prec } syn)
           pure []
  desugarDecl ps (PFixity fc fix prec n) 
      = do syn <- get Syn
           put Syn (record { infixes $= insert n (fix, prec) } syn)
           pure []
  desugarDecl ps (PNamespace fc ns decls)
      = pure [INamespace fc ns (concat !(traverse (desugarDecl ps) decls))]
  desugarDecl ps (PDirective fc d) 
      = case d of
             Logging i => pure [ILog i]
             LazyNames ty d f => pure [IPragma (\env, nest => setLazy fc ty d f)]
             PairNames ty f s => pure [IPragma (\env, nest => setPair fc ty f s)]

