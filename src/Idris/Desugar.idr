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

public export
record SyntaxInfo where
  constructor MkSyntax
  -- Keep infix/prefix, then we can define operators which are both
  -- (most obviously, -)
  infixes : StringMap (Fixity, Nat)
  prefixes : StringMap Nat

export
TTC annot Fixity where
  toBuf b InfixL = tag 0
  toBuf b InfixR = tag 1
  toBuf b Infix = tag 2
  toBuf b Prefix = tag 3

  fromBuf s b 
      = case !getTag of
             0 => pure InfixL
             1 => pure InfixR
             2 => pure Infix
             3 => pure Prefix
             _ => corrupt "Fixity"

export
TTC annot SyntaxInfo where
  toBuf b syn 
      = do toBuf b (toList (infixes syn))
           toBuf b (toList (prefixes syn))

  fromBuf s b 
      = do inf <- fromBuf s b
           pre <- fromBuf s b
           pure (MkSyntax (fromList inf) (fromList pre))

export
initSyntax : SyntaxInfo
initSyntax = MkSyntax empty empty

-- A label for Syntax info in the global state
export
data Syn : Type where

export
extend : {auto s : Ref Syn SyntaxInfo} ->
         SyntaxInfo -> Core annot ()
extend newsyn
    = do syn <- get Syn
         put Syn (record { infixes $= mergeLeft (infixes newsyn),
                           prefixes $= mergeLeft (prefixes newsyn) } syn)

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
            PTerm -> Core FC (RawImp FC)
  desugar (PRef fc x) = pure $ IVar fc x
  desugar (PPi fc rig p mn argTy retTy) 
      = pure $ IPi fc rig p mn !(desugar argTy) 
                               !(desugar retTy)
  desugar (PLam fc rig p n argTy scope) 
      = pure $ ILam fc rig p n !(desugar argTy) 
                               !(desugar scope)
  desugar (PLet fc rig (PRef _ n) nTy nVal scope [])
      = pure $ ILet fc rig n !(desugar nTy) !(desugar nVal) 
                             !(desugar scope)
  desugar (PLet fc rig pat nTy nVal scope alts) 
      = pure $ ICase fc !(desugar nVal) !(desugar nTy)
                        !(traverse (desugarClause True) 
                            (MkPatClause fc pat scope [] :: alts))
  desugar (PCase fc x xs) 
      = pure $ ICase fc !(desugar x) 
                        (Implicit fc)
                        !(traverse (desugarClause True) xs)
  desugar (PLocal fc xs scope) 
      = pure $ ILocal fc (concat !(traverse desugarDecl xs)) 
                         !(desugar scope)
  desugar (PApp fc x y) 
      = pure $ IApp fc !(desugar x) !(desugar y)
  desugar (PImplicitApp fc x argn y) 
      = pure $ IImplicitApp fc !(desugar x) argn !(desugar y)
  desugar (PEq fc l r)
      = do l' <- desugar l
           r' <- desugar r
           pure $ apply (IVar fc (UN "Equal")) [l', r']
  desugar (PBracketed fc e) = desugar e
  desugar (POp fc op l r) 
      = do ts <- toTokList (POp fc op l r)
           desugarTree !(parseOps ts)
  desugar (PPrefixOp fc op arg) 
      = do ts <- toTokList (PPrefixOp fc op arg)
           desugarTree !(parseOps ts)
  desugar (PSectionL fc op arg) 
      = do syn <- get Syn
           -- It might actually be a prefix argument rather than a section
           -- so check that first, otherwise desugar as a lambda
           case lookup op (prefixes syn) of
                Nothing => 
                   desugar (PLam fc RigW Explicit (MN "arg" 0) (PImplicit fc)
                               (POp fc op (PRef fc (MN "arg" 0)) arg))
                Just prec => desugar (PPrefixOp fc op arg)
  desugar (PSectionR fc arg op)
      = desugar (PLam fc RigW Explicit (MN "arg" 0) (PImplicit fc)
                 (POp fc op arg (PRef fc (MN "arg" 0))))
  desugar (PSearch fc depth) = pure $ ISearch fc depth
  desugar (PPrimVal fc (BI x))
      = pure $ IAlternative fc (UniqueDefault (IPrimVal fc (BI x)))
                               [IPrimVal fc (BI x), 
                                IPrimVal fc (I (fromInteger x))]
  desugar (PPrimVal fc x) = pure $ IPrimVal fc x
  desugar (PQuote fc x) = pure $ IQuote fc !(desugar x)
  desugar (PUnquote fc x) = pure $ IUnquote fc !(desugar x)
  desugar (PHole fc holename) = pure $ IHole fc holename
  desugar (PType fc) = pure $ IType fc
  desugar (PAs fc vname pattern) 
      = pure $ IAs fc vname !(desugar pattern)
  desugar (PDotted fc x) 
      = pure $ IMustUnify fc !(desugar x)
  desugar (PImplicit fc) = pure $ Implicit fc
  desugar (PDoBlock fc block)
      = expandDo fc block
  desugar (PList fc args)
      = expandList fc args
  desugar (PPair fc l r) 
      = do l' <- desugar l
           r' <- desugar r
           pure $ IAlternative fc Unique
                  [apply (IVar fc (UN "Pair")) [l', r'],
                   apply (IVar fc (UN "MkPair")) [l', r']]
  desugar (PUnit fc) 
      = pure $ IAlternative fc Unique 
               [IVar fc (UN "Unit"), 
                IVar fc (UN "MkUnit")]
  
  expandList : {auto s : Ref Syn SyntaxInfo} ->
               {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState FC)} ->
               FC -> List PTerm -> Core FC (RawImp FC)
  expandList fc [] = pure (IVar fc (UN "Nil"))
  expandList fc (x :: xs)
      = pure $ apply (IVar fc (UN "::")) [!(desugar x), !(expandList fc xs)]

  expandDo : {auto s : Ref Syn SyntaxInfo} ->
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState FC)} ->
             FC -> List PDo -> Core FC (RawImp FC)
  expandDo fc [] = throw (GenericMsg fc "Do block cannot be empty")
  expandDo _ [DoExp fc tm] = desugar tm
  expandDo fc [e] 
      = throw (GenericMsg (getLoc e) 
                  "Last statement in do block must be an expression") 
  expandDo topfc (DoExp fc tm :: rest)
      = do tm' <- desugar tm
           rest' <- expandDo topfc rest
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) tm')
                     (ILam fc RigW Explicit (UN "_") (Implicit fc) rest')
  expandDo topfc (DoBind fc n tm :: rest)
      = do tm' <- desugar tm
           rest' <- expandDo topfc rest
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) tm')
                     (ILam fc RigW Explicit n (Implicit fc) rest')
  expandDo topfc (DoBindPat fc pat exp alts :: rest)
      = do pat' <- desugar pat
           exp' <- desugar exp
           alts' <- traverse (desugarClause True) alts
           rest' <- expandDo topfc rest
           pure $ IApp fc (IApp fc (IVar fc (UN ">>=")) exp')
                    (ILam fc RigW Explicit (MN "_" 0) (Implicit fc)
                          (ICase fc (IVar fc (MN "_" 0))
                               (Implicit fc)
                               (PatClause fc (bindNames False [] pat') rest' 
                                  :: alts')))
  expandDo topfc (DoLet fc n rig tm :: rest) 
      = do tm' <- desugar tm
           rest' <- expandDo topfc rest
           pure $ ILet fc rig n (Implicit fc) tm' rest'
  expandDo topfc (DoLetPat fc pat tm alts :: rest) 
      = do pat' <- desugar pat
           tm' <- desugar tm
           alts' <- traverse (desugarClause True) alts
           rest' <- expandDo topfc rest
           pure $ ICase fc tm' (Implicit fc) 
                       (PatClause fc (bindNames False [] pat') rest'
                                  :: alts')
  expandDo topfc (DoLetLocal fc decls :: rest)
      = do rest' <- expandDo topfc rest
           decls' <- traverse desugarDecl decls
           pure $ ILocal fc (concat decls') rest'

  desugarTree : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                Tree FC PTerm -> Core FC (RawImp FC)
  desugarTree (Inf loc op l r)
      = do l' <- desugarTree l
           r' <- desugarTree r
           pure (IApp loc (IApp loc (IVar loc (UN op)) l') r')
  desugarTree (Pre loc op arg)
      = do arg' <- desugarTree arg
           pure (IApp loc (IVar loc (UN op)) arg')
  desugarTree (Leaf t) = desugar t

  desugarType : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                PTypeDecl -> Core FC (ImpTy FC)
  desugarType (MkPTy fc n ty) 
      = pure $ MkImpTy fc n (bindNames True [] !(desugar ty))

  desugarClause : {auto s : Ref Syn SyntaxInfo} ->
                  {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST (UState FC)} ->
                  Bool -> PClause -> Core FC (ImpClause FC)
  desugarClause arg (MkPatClause fc lhs rhs wheres)
      = do ws <- traverse desugarDecl wheres
           rhs' <- desugar rhs
           pure $ PatClause fc (bindNames arg [] !(desugar lhs)) 
                     (case ws of
                           [] => rhs'
                           _ => ILocal fc (concat ws) rhs')
  desugarClause arg (MkImpossible fc lhs) 
      = pure $ ImpossibleClause fc (bindNames arg [] !(desugar lhs))

  desugarData : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                PDataDecl -> Core FC (ImpData FC)
  desugarData (MkPData fc n tycon opts datacons) 
      = pure $ MkImpData fc n (bindNames True [] !(desugar tycon))
                              opts
                              !(traverse desugarType datacons)
  desugarData (MkPLater fc n tycon) 
      = pure $ MkImpLater fc n (bindNames True [] !(desugar tycon))

  -- Given a high level declaration, return a list of TTImp declarations
  -- which process it, and update any necessary state on the way.
  export
  desugarDecl : {auto s : Ref Syn SyntaxInfo} ->
                {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                PDecl -> Core FC (List (ImpDecl FC))
  desugarDecl (PClaim fc vis opts ty) 
      = pure [IClaim fc vis opts !(desugarType ty)]
  desugarDecl (PDef fc n clauses) 
      = pure [IDef fc n !(traverse (desugarClause False) clauses)]
  desugarDecl (PData fc vis ddecl) 
      = pure [IData fc vis !(desugarData ddecl)]
  desugarDecl (PReflect fc tm)
      = pure [IReflect fc !(desugar tm)]
  desugarDecl (PInterface fc vis cons tn params det conname body)
      = do cons' <- traverse (\ (n, tm) => do tm' <- desugar tm
                                              pure (n, tm')) cons
           params' <- traverse (\ (n, tm) => do tm' <- desugar tm
                                                pure (n, tm')) params
           body' <- traverse desugarDecl body
           pure [IPragma (\env, nest => 
                             elabInterface fc vis env nest cons' 
                                           tn params' det conname 
                                           (concat body'))]
  desugarDecl (PImplementation fc vis cons tn params impname body)
      = throw (InternalError "Implementations not done yet")
  desugarDecl (PFixity fc Prefix prec n) 
      = do syn <- get Syn
           put Syn (record { prefixes $= insert n prec } syn)
           pure []
  desugarDecl (PFixity fc fix prec n) 
      = do syn <- get Syn
           put Syn (record { infixes $= insert n (fix, prec) } syn)
           pure []
  desugarDecl (PNamespace fc ns decls)
      = pure [INamespace fc ns (concat !(traverse desugarDecl decls))]
  desugarDecl (PDirective fc d) 
      = case d of
             Logging i => pure [ILog i]
             LazyNames ty d f => pure [IPragma (\env, nest => setLazy fc ty d f)]

