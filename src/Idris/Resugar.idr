module Idris.Resugar

import Core.Context
import Core.Options

import Idris.Desugar
import Idris.Syntax

import TTImp.TTImp
import TTImp.Elab.Unelab

import Data.StringMap

%default covering

mkOp : {auto s : Ref Syn SyntaxInfo} ->
       PTerm -> Core FC PTerm
mkOp tm@(PApp fc (PApp _ (PRef _ n) x) y)
    = do syn <- get Syn
         case StringMap.lookup (nameRoot n) (infixes syn) of
              Nothing => pure tm
              Just _ => pure (POp fc (nameRoot n) x y)
mkOp tm = pure tm

bracket : {auto s : Ref Syn SyntaxInfo} ->
          (outer : Nat) -> (inner : Nat) -> PTerm -> Core FC PTerm
bracket outer inner tm
    = do tm' <- mkOp tm
         if outer > inner 
            then pure (PBracketed emptyFC tm')
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
         pure (show_implicits pp)

mutual
  toPTerm : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            (prec : Nat) -> RawImp annot -> Core FC PTerm
  toPTerm p (IVar _ n) 
      = do imp <- showImplicits
           pure (PRef emptyFC (if imp then n else dropNS n))
  toPTerm p (IPi _ rig Implicit n arg ret)
      = do imp <- showImplicits
           if imp
              then do arg' <- toPTerm tyPrec arg
                      ret' <- toPTerm p ret
                      bracket p startPrec (PPi emptyFC rig Implicit n arg' ret')
              else toPTerm p ret
  toPTerm p (IPi _ rig pt n arg ret)
      = do arg' <- toPTerm tyPrec arg
           ret' <- toPTerm p ret
           bracket p startPrec (PPi emptyFC rig pt n arg' ret')
  toPTerm p (ILam _ rig pt n arg sc)
      = do imp <- showImplicits
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
           bracket p startPrec (PLet emptyFC rig n ty' val' sc')
  toPTerm p (ICase _ sc alts)
      = do sc' <- toPTerm startPrec sc
           alts' <- traverse toPClause alts
           bracket p startPrec (PCase emptyFC sc' alts')
  toPTerm p (ILocal _ ds sc)
      = do ds' <- traverse toPDecl ds
           sc' <- toPTerm startPrec sc
           bracket p startPrec (PLocal emptyFC (mapMaybe id ds') sc')
  toPTerm p (IApp _ fn arg)
      = do fn' <- toPTerm appPrec fn
           arg' <- toPTerm argPrec arg
           bracket p appPrec (PApp emptyFC fn' arg')
  toPTerm p (IImplicitApp _ fn n arg) 
      = do imp <- showImplicits
           if imp
              then do fn' <- toPTerm appPrec fn
                      arg' <- toPTerm startPrec arg
                      bracket p startPrec (PImplicitApp emptyFC fn' n arg')
              else do fn' <- toPTerm p fn
                      mkOp fn'

  toPTerm p (ISearch _ d) = pure (PSearch emptyFC d)
  toPTerm p (IAlternative _ _ _) = pure (PImplicit emptyFC)
  toPTerm p (ICoerced _ tm) = toPTerm p tm
  toPTerm p (IPrimVal _ c) = pure (PPrimVal emptyFC c)
  toPTerm p (IHole _ str) = pure (PHole emptyFC str)
  toPTerm p (IType _) = pure (PType emptyFC)
  toPTerm p (IBindVar _ v) = pure (PRef emptyFC (UN v))
  toPTerm p (IAs _ n pat) = pure (PAs emptyFC n !(toPTerm argPrec pat))
  toPTerm p (IMustUnify _ pat) = pure (PDotted emptyFC !(toPTerm argPrec pat))
  toPTerm p (Implicit _) = pure (PImplicit emptyFC)

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

  toPDecl : {auto c : Ref Ctxt Defs} ->
            {auto s : Ref Syn SyntaxInfo} ->
            ImpDecl annot -> Core FC (Maybe PDecl)
  toPDecl (IClaim _ vis opts ty) 
      = pure (Just (PClaim emptyFC vis opts !(toPTypeDecl ty)))
  toPDecl (IDef _ n cs)
      = pure (Just (PDef emptyFC n !(traverse toPClause cs)))
  toPDecl (IData _ vis d)
      = pure (Just (PData emptyFC vis !(toPData d)))
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
    = do tti <- unelab env tm
         toPTerm startPrec tti

export
Show PTerm where
  show (PRef _ n) = show n
  show (PPi _ rig Explicit Nothing arg ret)
      = show arg ++ " -> " ++ show ret
  show (PPi _ rig Explicit (Just n) arg ret)
      = "(" ++ show n ++ " : " ++ show arg ++ ") -> " ++ show ret
  show (PPi _ rig Implicit Nothing arg ret) -- shouldn't happen
      = "{_ : " ++ show arg ++ "} -> " ++ show ret
  show (PPi _ rig Implicit (Just n) arg ret)
      = "{" ++ show n ++ " : " ++ show arg ++ "} -> " ++ show ret
  show (PPi _ rig AutoImplicit Nothing arg ret) -- shouldn't happen
      = "{auto _ : " ++ show arg ++ "} -> " ++ show ret
  show (PPi _ rig AutoImplicit (Just n) arg ret)
      = "{auto " ++ show n ++ " : " ++ show arg ++ "} -> " ++ show ret
  show (PLam _ rig _ n (PImplicit _) sc)
      = "\\" ++ show n ++ " => " ++ show sc
  show (PLam _ rig _ n ty sc)
      = "\\" ++ show n ++ " : " ++ show ty ++ " => " ++ show sc
  show (PLet _ rig n (PImplicit _) val sc)
      = "let " ++ show n ++ " = " ++ show val ++ " in " ++ show sc
  show (PLet _ rig n ty val sc)
      = "let " ++ show n ++ " : " ++ show ty ++ " = " 
               ++ show val ++ " in " ++ show sc
  show (PCase _ tm cs) 
      = "case " ++ show tm ++ " of { " ++ 
          showSep " ; " (map showCase cs) ++ " }"
    where
      showCase : PClause -> String
      showCase (MkPatClause _ lhs rhs _) = show lhs ++ " => " ++ show rhs
      showCase (MkImpossible _ lhs) = show lhs ++ " impossible"
  show (PLocal _ ds sc) -- We'll never see this when displaying a normal form...
      = "let { << definitions >>  } in " ++ show sc
  show (PApp _ f a) = show f ++ " " ++ show a
  show (PImplicitApp _ f n (PRef _ a)) 
      = if n == a
           then show f ++ " {" ++ show n ++ "}"
           else show f ++ " {" ++ show n ++ " = " ++ show a ++ "}"
  show (PImplicitApp _ f n a) 
      = show f ++ " {" ++ show n ++ " = " ++ show a ++ "}"
  show (PSearch _ d) = "%search"
  show (PPrimVal _ c) = show c
  show (PHole _ n) = "?" ++ n
  show (PType _) = "Type"
  show (PAs _ n p) = n ++ "@" ++ show p
  show (PDotted _ p) = "." ++ show p
  show (PImplicit _) = "_"
  show (POp _ op x y) = show x ++ " " ++ op ++ " " ++ show y
  show (PPrefixOp _ op x) = op ++ show x
  show (PSectionL _ op x) = "(" ++ op ++ " " ++ show x ++ ")"
  show (PSectionR _ x op) = "(" ++ show x ++ " " ++ op ++ ")"
  show (PBracketed _ tm) = "(" ++ show tm ++ ")"
  show (PDoBlock _ ds) 
      = "do " ++ showSep " ; " (map showDo ds)
    where
      showAlt : PClause -> String
      showAlt (MkPatClause _ lhs rhs _) = " | " ++ show lhs ++ " => " ++ show rhs ++ ";"
      showAlt (MkImpossible _ lhs) = " | " ++ show lhs ++ " impossible;"

      showDo : PDo -> String
      showDo (DoExp _ tm) = show tm
      showDo (DoBind _ n tm) = show n ++ " <- " ++ show tm
      showDo (DoBindPat _ l tm alts) 
          = show l ++ " <- " ++ show tm ++ concatMap showAlt alts
      showDo (DoLet _ l rig tm) = "let " ++ show l ++ " = " ++ show tm
      showDo (DoLetPat _ l tm alts) 
          = "let " ++ show l ++ " = " ++ show tm ++ concatMap showAlt alts

  show (PPair _ l r) = "(" ++ show l ++ ", " ++ show r ++ ")"
  show (PUnit _) = "()"
