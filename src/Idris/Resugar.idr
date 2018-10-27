module Idris.Resugar

import Core.Context
import Core.Options

import Idris.Syntax

import TTImp.TTImp
import TTImp.Elab.Unelab

import Data.StringMap

%default covering

-- Convert checked terms back to source syntax. Note that this is entirely
-- for readability therefore there is NO GUARANTEE that the result will
-- type check (in fact it probably won't due to tidying up names for
-- readability).

unbracketApp : PTerm -> PTerm
unbracketApp (PBracketed _ tm@(PApp _ _ _)) = tm
unbracketApp tm = tm

-- TODO: Deal with precedences
mkOp : {auto s : Ref Syn SyntaxInfo} ->
       PTerm -> Core FC PTerm
mkOp tm@(PApp fc (PApp _ (PRef _ n) x) y)
    = do syn <- get Syn
         case StringMap.lookup (nameRoot n) (infixes syn) of
              Nothing => pure tm
              Just _ => pure (POp fc (nameRoot n) (unbracketApp x) (unbracketApp y))
mkOp tm = pure tm

export
addBracket : FC -> PTerm -> PTerm
addBracket fc tm = if needed tm then PBracketed fc tm else tm
  where
    needed : PTerm -> Bool
    needed (PBracketed _ _) = False
    needed (PPair _ _ _) = False
    needed (PUnit _) = False
    needed (PComprehension _ _ _) = False
    needed (PList _ _) = False
    needed tm = True

bracket : {auto s : Ref Syn SyntaxInfo} ->
          (outer : Nat) -> (inner : Nat) -> PTerm -> Core FC PTerm
bracket outer inner tm
    = do tm' <- mkOp tm
         if outer > inner
            then pure (addBracket emptyFC tm')
            else pure tm'

startPrec : Nat
startPrec = 0

tyPrec : Nat
tyPrec = 1

appPrec : Nat
appPrec = 999

argPrec : Nat
argPrec = 1000

showImplicits : {auto c : Ref Ctxt Defs} ->
                Core annot Bool
showImplicits
    = do pp <- getPPrint
         pure (showImplicits pp)

fullNamespace : {auto c : Ref Ctxt Defs} ->
                Core annot Bool
fullNamespace
    = do pp <- getPPrint
         pure (fullNamespace pp)

unbracket : PTerm -> PTerm
unbracket (PBracketed _ tm) = tm
unbracket tm = tm

-- Put the special names (Nil, ::, Pair etc) back as syntax
sugarApp : PTerm -> PTerm
sugarApp (PApp fc (PApp _ (PRef _ (UN "Pair")) l) r)
    = PPair fc (unbracket l) (unbracket r)
sugarApp (PApp fc (PApp _ (PRef _ (UN "MkPair")) l) r)
    = PPair fc (unbracket l) (unbracket r)
sugarApp (PApp fc (PApp _ (PRef _ (UN "Equal")) l) r)
    = PEq fc l r
sugarApp (PRef fc (UN "Nil")) = PList fc []
sugarApp (PRef fc (UN "Unit")) = PUnit fc
sugarApp (PRef fc (UN "MkUnit")) = PUnit fc
sugarApp tm@(PApp fc (PApp _ (PRef _ (UN "::")) x) xs)
    = case sugarApp (unbracket xs) of
           PList fc xs' => PList fc (unbracketApp x :: xs')
           _ => tm
sugarApp tm = tm

export
sugarName : Name -> Name
sugarName (MN n _) = UN n
sugarName (PV n _) = sugarName n
sugarName (DN n _) = UN n
sugarName x = x

mutual
  toPTerm : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            (prec : Nat) -> RawImp annot -> Core FC PTerm
  toPTerm p (IVar _ (MN n _))
      = pure (sugarApp (PRef emptyFC (UN n)))
  toPTerm p (IVar _ (PV n _))
      = pure (sugarApp (PRef emptyFC n))
  toPTerm p (IVar _ (DN n _))
      = pure (sugarApp (PRef emptyFC (UN n)))
  toPTerm p (IVar loc (GN (Nested _ n)))
      = toPTerm p (IVar loc n)
  toPTerm p (IVar _ n) 
      = do ns <- fullNamespace
           pure (sugarApp (PRef emptyFC (if ns then n else dropNS n)))
  toPTerm p (IPi _ rig Implicit n arg ret)
      = do imp <- showImplicits
           if imp
              then do arg' <- toPTerm appPrec arg
                      ret' <- toPTerm tyPrec ret
                      bracket p tyPrec (PPi emptyFC rig Implicit n arg' ret')
              else toPTerm p ret
  toPTerm p (IPi _ rig pt n arg ret)
      = do arg' <- toPTerm appPrec arg
           ret' <- toPTerm tyPrec ret
           bracket p tyPrec (PPi emptyFC rig pt n arg' ret')
  toPTerm p (ILam _ rig pt mn arg sc)
      = do let n = case mn of
                        Nothing => UN "_"
                        Just n' => n'
           imp <- showImplicits
           arg' <- if imp then toPTerm tyPrec arg
                          else pure (PImplicit emptyFC)
           sc' <- toPTerm p sc
           bracket p startPrec (PLam emptyFC rig pt n arg' sc')
  toPTerm p (ILet _ rig n ty val sc)
      = do imp <- showImplicits
           ty' <- if imp then toPTerm startPrec ty
                         else pure (PImplicit emptyFC)
           val' <- toPTerm startPrec val
           sc' <- toPTerm startPrec sc
           bracket p startPrec (PLet emptyFC rig (PRef emptyFC n)
                                     ty' val' sc' [])
  toPTerm p (ICase _ sc scty alts)
      = do sc' <- toPTerm startPrec sc
           alts' <- traverse toPClause alts
           bracket p startPrec (mkIf (PCase emptyFC sc' alts'))
    where
      mkIf : PTerm -> PTerm
      mkIf tm@(PCase loc sc [MkPatClause _ (PRef _ tval) t [], 
                             MkPatClause _ (PRef _ fval) f []])
         = if dropNS tval == UN "True" && dropNS fval == UN "False"
              then PIfThenElse loc sc t f
              else tm
      mkIf tm = tm
  toPTerm p (ILocal _ ds sc)
      = do ds' <- traverse toPDecl ds
           sc' <- toPTerm startPrec sc
           bracket p startPrec (PLocal emptyFC (mapMaybe id ds') sc')
  toPTerm p tm@(IApp _ fn arg)
      = do arg' <- toPTerm argPrec arg
           app <- toPTermApp fn [(Nothing, arg')]
           bracket p appPrec app
  toPTerm p (IImplicitApp _ fn n arg) 
      = do arg' <- toPTerm startPrec arg
           app <- toPTermApp fn [(Just n, arg')]
           imp <- showImplicits
           if imp
              then bracket p startPrec app
              else mkOp app
  toPTerm p (ISearch _ d) = pure (PSearch emptyFC d)
  toPTerm p (IAlternative _ _ _) = pure (PImplicit emptyFC)
  toPTerm p (IRewrite _ rule tm) 
      = pure (PRewrite emptyFC !(toPTerm startPrec rule)
                               !(toPTerm startPrec tm))
  toPTerm p (ICoerced _ tm) = toPTerm p tm
  toPTerm p (IPrimVal _ c) = pure (PPrimVal emptyFC c)
  toPTerm p (IQuote _ tm) = pure (PQuote emptyFC !(toPTerm startPrec tm))
  toPTerm p (IUnquote _ tm) = pure (PUnquote emptyFC !(toPTerm startPrec tm))
  toPTerm p (IHole _ str) = pure (PHole emptyFC False str)
  toPTerm p (IType _) = pure (PType emptyFC)
  toPTerm p (IBindVar _ v) = pure (PRef emptyFC (UN v))
  toPTerm p (IBindHere _ tm) = toPTerm p tm
  toPTerm p (IAs _ n pat) = pure (PAs emptyFC n !(toPTerm argPrec pat))
  toPTerm p (IMustUnify _ r pat) = pure (PDotted emptyFC !(toPTerm argPrec pat))
  toPTerm p (Implicit _) = pure (PImplicit emptyFC)
  toPTerm p (Infer _) = pure (PInfer emptyFC)

  mkApp : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          PTerm -> List (Maybe (Maybe Name), PTerm) -> Core FC PTerm
  mkApp fn [] = pure fn 
  mkApp fn ((Nothing, arg) :: rest)
      = do let ap = sugarApp (PApp emptyFC fn arg)
           mkApp ap rest
  mkApp fn ((Just n, arg) :: rest)
      = do imp <- showImplicits
           if imp
              then do let ap = PImplicitApp emptyFC fn n arg
                      mkApp ap rest
              else mkApp fn rest

  toPTermApp : {auto c : Ref Ctxt Defs} ->
               {auto s : Ref Syn SyntaxInfo} ->
               RawImp annot -> List (Maybe (Maybe Name), PTerm) ->
               Core FC PTerm
  toPTermApp (IApp _ f a) args 
      = do a' <- toPTerm argPrec a
           toPTermApp f ((Nothing, a') :: args)
  toPTermApp (IImplicitApp _ f n a) args 
      = do a' <- toPTerm startPrec a
           toPTermApp f ((Just n, a') :: args)
  toPTermApp fn@(IVar _ n) args
      = do defs <- get Ctxt
           case lookupGlobalExact n (gamma defs) of
                Nothing => do fn' <- toPTerm appPrec fn
                              mkApp fn' args
                Just def => do fn' <- toPTerm appPrec fn
                               mkApp fn' (drop (length (vars def)) args)
  toPTermApp fn args 
      = do fn' <- toPTerm appPrec fn
           mkApp fn' args

  toPClause : {auto c : Ref Ctxt Defs} ->
              {auto s : Ref Syn SyntaxInfo} ->
              ImpClause annot -> Core FC PClause
  toPClause (PatClause _ lhs rhs)
      = pure (MkPatClause emptyFC !(toPTerm startPrec lhs)
                                  !(toPTerm startPrec rhs)
                                  [])
  toPClause (ImpossibleClause _ lhs)
      = pure (MkImpossible emptyFC !(toPTerm startPrec lhs))

  toPTypeDecl : {auto c : Ref Ctxt Defs} ->
                {auto s : Ref Syn SyntaxInfo} ->
                ImpTy annot -> Core FC PTypeDecl
  toPTypeDecl (MkImpTy _ n ty)
      = pure (MkPTy emptyFC n !(toPTerm startPrec ty))

  toPData : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            ImpData annot -> Core FC PDataDecl
  toPData (MkImpData _ n ty opts cs)
      = pure (MkPData emptyFC n !(toPTerm startPrec ty) opts
                   !(traverse toPTypeDecl cs))
  toPData (MkImpLater _ n ty)
      = pure (MkPLater emptyFC n !(toPTerm startPrec ty))

  toPDecl : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            ImpDecl annot -> Core FC (Maybe PDecl)
  toPDecl (IClaim _ vis opts ty) 
      = pure (Just (PClaim emptyFC vis opts !(toPTypeDecl ty)))
  toPDecl (IDef _ n cs)
      = pure (Just (PDef emptyFC !(traverse toPClause cs)))
  toPDecl (IData _ vis d)
      = pure (Just (PData emptyFC vis !(toPData d)))
  toPDecl (IReflect _ tm)
      = pure (Just (PReflect emptyFC !(toPTerm startPrec tm)))
  toPDecl (INamespace _ ns ds)
      = do ds' <- traverse toPDecl ds
           pure (Just (PNamespace emptyFC ns (mapMaybe id ds')))
  toPDecl (ImplicitNames _ _) = pure Nothing
  toPDecl (IHint _ _ _) = pure Nothing
  toPDecl (IPragma _) = pure Nothing
  toPDecl (ILog _) = pure Nothing

export
resugar : {auto c : Ref Ctxt Defs} ->
          {auto s : Ref Syn SyntaxInfo} ->
          Env Term vars -> Term vars -> Core FC PTerm
resugar env tm
    = do tti <- unelab emptyFC env tm
         toPTerm startPrec tti
        
export
pterm : {auto c : Ref Ctxt Defs} ->
        {auto s : Ref Syn SyntaxInfo} ->
        RawImp FC -> Core FC PTerm
pterm raw = toPTerm startPrec raw
