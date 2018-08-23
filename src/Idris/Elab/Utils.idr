module Idris.Elab.Utils

import Core.TT

import Idris.BindImplicits
import Idris.Syntax

import TTImp.TTImp

mutual
  export
  substNames : List Name -> List (Name, RawImp FC) -> RawImp FC -> RawImp FC
  substNames bound ps (IVar fc n) 
      = if not (n `elem` bound)
           then case lookup n ps of
                     Just t => t
                     _ => IVar fc n
           else IVar fc n
  substNames bound ps (IPi fc r p mn argTy retTy) 
      = let bound' = maybe bound (\n => n :: bound) mn in
            IPi fc r p mn (substNames bound ps argTy) 
                          (substNames bound' ps retTy)
  substNames bound ps (ILam fc r p mn argTy scope)
      = let bound' = maybe bound (\n => n :: bound) mn in
            ILam fc r p mn (substNames bound ps argTy) 
                           (substNames bound' ps scope)
  substNames bound ps (ILet fc r n nTy nVal scope)
      = let bound' = n :: bound in
            ILet fc r n (substNames bound ps nTy) 
                        (substNames bound ps nVal)
                        (substNames bound' ps scope)
  substNames bound ps (ICase fc y ty xs) 
      = ICase fc (substNames bound ps y) (substNames bound ps ty)
                 (map (substNamesClause bound ps) xs)
  substNames bound ps (ILocal fc xs y) 
      = let bound' = definedInBlock xs ++ bound in
            ILocal fc (map (substNamesDecl bound ps) xs) 
                      (substNames bound' ps y)
  substNames bound ps (IApp fc fn arg) 
      = IApp fc (substNames bound ps fn) (substNames bound ps arg)
  substNames bound ps (IImplicitApp fc fn y arg)
      = IImplicitApp fc (substNames bound ps fn) y (substNames bound ps arg)
  substNames bound ps (IAlternative fc y xs) 
      = IAlternative fc y (map (substNames bound ps) xs)
  substNames bound ps (ICoerced fc y) 
      = ICoerced fc (substNames bound ps y)
  substNames bound ps (IQuote fc y)
      = IQuote fc (substNames bound ps y)
  substNames bound ps (IUnquote fc y)
      = IUnquote fc (substNames bound ps y)
  substNames bound ps (IAs fc y pattern)
      = IAs fc y (substNames bound ps pattern)
  substNames bound ps (IMustUnify fc r pattern)
      = IMustUnify fc r (substNames bound ps pattern)
  substNames bound ps tm = tm

  substNamesClause : List Name -> List (Name, RawImp FC) -> 
                      ImpClause FC -> ImpClause FC
  substNamesClause bound ps (PatClause fc lhs rhs)
      = let bound' = map UN (map snd (findBindableNames True bound [] lhs))
                        ++ bound in
            PatClause fc (substNames [] [] lhs) 
                         (substNames bound' ps rhs)
  substNamesClause bound ps (ImpossibleClause fc lhs)
      = ImpossibleClause fc (substNames bound [] lhs)

  substNamesTy : List Name -> List (Name, RawImp FC) ->
                  ImpTy FC -> ImpTy FC
  substNamesTy bound ps (MkImpTy fc n ty) 
      = MkImpTy fc n (substNames bound ps ty)
  
  substNamesData : List Name -> List (Name, RawImp FC) ->
                    ImpData FC -> ImpData FC
  substNamesData bound ps (MkImpData fc n con opts dcons) 
      = MkImpData fc n (substNames bound ps con) opts
                  (map (substNamesTy bound ps) dcons)
  substNamesData bound ps (MkImpLater fc n con) 
      = MkImpLater fc n (substNames bound ps con)

  substNamesDecl : List Name -> List (Name, RawImp FC) ->
                    ImpDecl FC -> ImpDecl FC
  substNamesDecl bound ps (IClaim fc vis opts td) 
      = IClaim fc vis opts (substNamesTy bound ps td)
  substNamesDecl bound ps (IDef fc n cs) 
      = IDef fc n (map (substNamesClause bound ps) cs)
  substNamesDecl bound ps (IData fc vis d) 
      = IData fc vis (substNamesData bound ps d)
  substNamesDecl bound ps (INamespace fc ns ds) 
      = INamespace fc ns (map (substNamesDecl bound ps) ds)
  substNamesDecl bound ps (IReflect fc y) 
      = IReflect fc (substNames bound ps y)
  substNamesDecl bound ps (ImplicitNames fc xs) 
      = ImplicitNames fc (map (\ (n, t) => (n, substNames bound ps t)) xs)
  substNamesDecl bound ps d = d


