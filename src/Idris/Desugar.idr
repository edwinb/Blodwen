module Idris.Desugar

import Core.Binary
import Core.Context
import Core.Core
import Core.TT

import Data.StringMap

import Idris.Syntax

import TTImp.TTImp

-- Convert high level Idris declarations (PDecl from Idris.Syntax) into
-- TTImp, recording any high level syntax info on the way (e.g. infix
-- operators)

-- Desugaring from high level Idris syntax to TTImp involves:

-- Done:

-- Still TODO:
-- * Shunting infix operators into function applications according to precedence
-- * Replacing 'do' notating with applications of (>>=)
-- * Replacing !-notation
-- * Replacing pattern matching binds with 'case'

%default covering

export
record SyntaxInfo where
  constructor MkSyntax
  infixes : StringMap (Fixity, Nat)

export
TTC annot Fixity where
  toBuf b InfixL = tag 0
  toBuf b InfixR = tag 1
  toBuf b Infix = tag 2

  fromBuf s b 
      = case !getTag of
             0 => pure InfixL
             1 => pure InfixR
             2 => pure Infix
             _ => corrupt "Fixity"

export
TTC annot SyntaxInfo where
  toBuf b syn = toBuf b (toList (infixes syn))
  fromBuf s b 
      = do inf <- fromBuf s b
           pure (MkSyntax (fromList inf))

export
initSyntax : SyntaxInfo
initSyntax = MkSyntax empty

-- A label for Syntax info in the global state
export
data Syn : Type where

mutual
  export
  desugar : {auto s : Ref Syn SyntaxInfo} ->
            PTerm -> Core FC (RawImp FC)
  desugar (PRef fc x) = pure $ IVar fc x
  desugar (PPi fc p n argTy retTy) 
      = pure $ IPi fc p n !(desugar argTy) !(desugar retTy)
  desugar (PLam fc p n argTy scope) 
      = pure $ ILam fc p n !(desugar argTy) !(desugar scope)
  desugar (PLet fc n nTy nVal scope) 
      = pure $ ILet fc n !(desugar nTy) !(desugar nVal) !(desugar scope)
  desugar (PCase fc x xs) 
      = pure $ ICase fc !(desugar x) !(traverse desugarClause xs)
  desugar (PLocal fc xs scope) 
      = pure $ ILocal fc (concat !(traverse desugarDecl xs)) !(desugar scope)
  desugar (PApp fc x y) 
      = pure $ IApp fc !(desugar x) !(desugar y)
  desugar (PImplicitApp fc x argn y) 
      = pure $ IImplicitApp fc !(desugar x) argn !(desugar y)
  desugar (PSearch fc depth) = pure $ ISearch fc depth
  desugar (PPrimVal fc x) = pure $ IPrimVal fc x
  desugar (PHole fc holename) = pure $ IHole fc holename
  desugar (PType fc) = pure $ IType fc
  desugar (PAs fc vname pattern) 
      = pure $ IAs fc vname !(desugar pattern)
  desugar (PDotted fc x) 
      = pure $ IMustUnify fc !(desugar x)
  desugar (PImplicit fc) = pure $ Implicit fc

  export
  desugarType : {auto s : Ref Syn SyntaxInfo} ->
                PTypeDecl -> Core FC (ImpTy FC)
  desugarType (MkPTy fc n ty) = pure $ MkImpTy fc n !(desugar ty)

  export
  desugarClause : {auto s : Ref Syn SyntaxInfo} ->
                  PClause -> Core FC (ImpClause FC)
  desugarClause (MkPatClause fc lhs rhs) 
      = pure $ PatClause fc !(desugar lhs) !(desugar rhs)
  desugarClause (MkImpossible fc lhs) 
      = pure $ ImpossibleClause fc !(desugar lhs)

  export
  desugarData : {auto s : Ref Syn SyntaxInfo} ->
                PDataDecl -> Core FC (ImpData FC)
  desugarData (MkPData fc n tycon datacons) 
      = pure $ MkImpData fc n !(desugar tycon) !(traverse desugarType datacons)

  -- Given a high level declaration, return a list of TTImp declarations
  -- which process it, and update any necessary state on the way.
  export
  desugarDecl : {auto s : Ref Syn SyntaxInfo} ->
                PDecl -> Core FC (List (ImpDecl FC))
  desugarDecl (PClaim fc ty) 
      = pure [IClaim fc !(desugarType ty)]
  desugarDecl (PDef fc n clauses) 
      = pure [IDef fc n !(traverse desugarClause clauses)]
  desugarDecl (PData fc ddecl) 
      = pure [IData fc !(desugarData ddecl)]
  desugarDecl (PInfix fc fix prec n) 
      = pure []
  desugarDecl (PDirective fc d) 
      = case d of
             Logging i => pure [ILog i]

