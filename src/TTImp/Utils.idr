module TTImp.Utils

import Core.Context
import Core.TT
import TTImp.TTImp

lowerFirst : String -> Bool
lowerFirst "" = False
lowerFirst str = assert_total (isLower (strHead str))

getUnique : List String -> String -> String
getUnique xs x = if x `elem` xs then getUnique xs (x ++ "'") else x

-- Bind lower case names in argument position
-- Don't go under case, let, or local bindings, or IAlternative
export
findBindableNames : (arg : Bool) -> List Name -> (used : List String) ->
                    RawImp annot -> List (String, String)
findBindableNames True env used (IVar fc (UN n))
    = if not (UN n `elem` env) && lowerFirst n
         then [(n, getUnique used n)]
         else []
findBindableNames arg env used (IPi fc rig p mn aty retty)
    = let env' = case mn of
                      Nothing => env
                      Just n => n :: env in
          findBindableNames True env' used aty ++
          findBindableNames True env' used retty
findBindableNames arg env used (ILam fc rig p mn aty sc)
    = let env' = case mn of
                      Nothing => env
                      Just n => n :: env in
      findBindableNames True env' used aty ++
      findBindableNames True env' used sc
findBindableNames arg env used (IApp fc fn av)
    = findBindableNames False env used fn ++ findBindableNames True env used av
findBindableNames arg env used (IImplicitApp fc fn n av)
    = findBindableNames False env used fn ++ findBindableNames True env used av
findBindableNames arg env used (IAs fc (UN n) pat)
    = (n, getUnique used n) :: findBindableNames arg env used pat
findBindableNames arg env used (IAs fc n pat)
    = findBindableNames arg env used pat
findBindableNames arg env used (IMustUnify fc r pat)
    = findBindableNames arg env used pat
findBindableNames arg env used (IAlternative fc u alts)
    = concatMap (findBindableNames arg env used) alts
-- We've skipped case, let and local - rather than guess where the
-- name should be bound, leave it to the programmer
findBindableNames arg env used tm = []


mutual
  export
  substNames : List Name -> List (Name, RawImp annot) -> 
               RawImp annot -> RawImp annot
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

  substNamesClause : List Name -> List (Name, RawImp annot) -> 
                      ImpClause annot -> ImpClause annot
  substNamesClause bound ps (PatClause fc lhs rhs)
      = let bound' = map UN (map snd (findBindableNames True bound [] lhs))
                        ++ bound in
            PatClause fc (substNames [] [] lhs) 
                         (substNames bound' ps rhs)
  substNamesClause bound ps (WithClause fc lhs wval cs)
      = let bound' = map UN (map snd (findBindableNames True bound [] lhs))
                        ++ bound in
            WithClause fc (substNames [] [] lhs) 
                          (substNames bound' ps wval) cs
  substNamesClause bound ps (ImpossibleClause fc lhs)
      = ImpossibleClause fc (substNames bound [] lhs)

  substNamesTy : List Name -> List (Name, RawImp annot) ->
                  ImpTy annot -> ImpTy annot
  substNamesTy bound ps (MkImpTy fc n ty) 
      = MkImpTy fc n (substNames bound ps ty)
  
  substNamesData : List Name -> List (Name, RawImp annot) ->
                    ImpData annot -> ImpData annot
  substNamesData bound ps (MkImpData fc n con opts dcons) 
      = MkImpData fc n (substNames bound ps con) opts
                  (map (substNamesTy bound ps) dcons)
  substNamesData bound ps (MkImpLater fc n con) 
      = MkImpLater fc n (substNames bound ps con)

  substNamesDecl : List Name -> List (Name, RawImp annot) ->
                    ImpDecl annot -> ImpDecl annot
  substNamesDecl bound ps (IClaim fc r vis opts td) 
      = IClaim fc r vis opts (substNamesTy bound ps td)
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

mutual
  export
  substLoc : annot -> RawImp annot -> RawImp annot
  substLoc fc' (IVar fc n) = IVar fc' n
  substLoc fc' (IPi fc r p mn argTy retTy) 
      = IPi fc' r p mn (substLoc fc' argTy) 
                      (substLoc fc' retTy)
  substLoc fc' (ILam fc r p mn argTy scope)
      = ILam fc' r p mn (substLoc fc' argTy) 
                        (substLoc fc' scope)
  substLoc fc' (ILet fc r n nTy nVal scope)
      = ILet fc' r n (substLoc fc' nTy) 
                     (substLoc fc' nVal)
                     (substLoc fc' scope)
  substLoc fc' (ICase fc y ty xs) 
      = ICase fc' (substLoc fc' y) (substLoc fc' ty)
                  (map (substLocClause fc') xs)
  substLoc fc' (ILocal fc xs y) 
      = ILocal fc' (map (substLocDecl fc') xs) 
                   (substLoc fc' y)
  substLoc fc' (IApp fc fn arg) 
      = IApp fc' (substLoc fc' fn) (substLoc fc' arg)
  substLoc fc' (IImplicitApp fc fn y arg)
      = IImplicitApp fc' (substLoc fc' fn) y (substLoc fc' arg)
  substLoc fc' (IAlternative fc y xs) 
      = IAlternative fc' y (map (substLoc fc') xs)
  substLoc fc' (ICoerced fc y) 
      = ICoerced fc' (substLoc fc' y)
  substLoc fc' (IQuote fc y)
      = IQuote fc' (substLoc fc' y)
  substLoc fc' (IUnquote fc y)
      = IUnquote fc' (substLoc fc' y)
  substLoc fc' (IAs fc y pattern)
      = IAs fc' y (substLoc fc' pattern)
  substLoc fc' (IMustUnify fc r pattern)
      = IMustUnify fc' r (substLoc fc' pattern)
  substLoc fc' tm = tm

  export
  substLocClause : annot -> ImpClause annot -> ImpClause annot
  substLocClause fc' (PatClause fc lhs rhs)
      = PatClause fc' (substLoc fc' lhs) 
                      (substLoc fc' rhs)
  substLocClause fc' (ImpossibleClause fc lhs)
      = ImpossibleClause fc' (substLoc fc' lhs)

  substLocTy : annot -> ImpTy annot -> ImpTy annot
  substLocTy fc' (MkImpTy fc n ty) 
      = MkImpTy fc' n (substLoc fc' ty)
  
  substLocData : annot -> ImpData annot -> ImpData annot
  substLocData fc' (MkImpData fc n con opts dcons) 
      = MkImpData fc' n (substLoc fc' con) opts
                        (map (substLocTy fc') dcons)
  substLocData fc' (MkImpLater fc n con) 
      = MkImpLater fc' n (substLoc fc' con)

  substLocDecl : annot -> ImpDecl annot -> ImpDecl annot
  substLocDecl fc' (IClaim fc r vis opts td) 
      = IClaim fc' r vis opts (substLocTy fc' td)
  substLocDecl fc' (IDef fc n cs) 
      = IDef fc' n (map (substLocClause fc') cs)
  substLocDecl fc' (IData fc vis d) 
      = IData fc' vis (substLocData fc' d)
  substLocDecl fc' (INamespace fc ns ds) 
      = INamespace fc' ns (map (substLocDecl fc') ds)
  substLocDecl fc' (IReflect fc y) 
      = IReflect fc' (substLoc fc' y)
  substLocDecl fc' (ImplicitNames fc xs) 
      = ImplicitNames fc' (map (\ (n, t) => (n, substLoc fc' t)) xs)
  substLocDecl fc' d = d


nameNum : String -> (String, Int)
nameNum str
    = case span isDigit (reverse str) of
           ("", _) => (str, 0)
           (nums, pre)
              => case unpack pre of
                      ('_' :: rest) => (reverse (pack rest), cast (reverse nums))
                      _ => (str, 0)

export
uniqueName : Defs -> List String -> String -> String
uniqueName defs used n
    = if usedName 
         then uniqueName defs used (next n)
         else n
  where
    usedName : Bool
    usedName 
        = case lookupTyName (UN n) (gamma defs) of
               [] => n `elem` used
               _ => True

    next : String -> String
    next str 
        = let (n, i) = nameNum str in
              n ++ "_" ++ show (i + 1)

matchFail : annot -> Core annot a
matchFail loc = throw (GenericMsg loc "Clauses do not match")

mutual
  export
  getMatch : RawImp annot -> RawImp annot ->
             Core annot (List (String, RawImp annot))
  getMatch (IBindVar _ n) tm = pure [(n, tm)]
  getMatch (Implicit _) tm = pure []
  getMatch (Infer _) tm = pure []

  getMatch (IVar _ n) (IVar loc n') 
      = if n == n' then pure [] else matchFail loc
  getMatch (IPi _ c p n arg ret) (IPi loc c' p' n' arg' ret')
      = if c == c' && p == p' && n == n'
           then matchAll [(arg, arg'), (ret, ret')]
           else matchFail loc
  -- TODO: Lam, Let, Case, Local, Update
  getMatch (IApp _ f a) (IApp loc f' a')
      = matchAll [(f, f'), (a, a')]
  getMatch (IImplicitApp _ f n a) (IImplicitApp loc f' n' a')
      = if n == n' 
           then matchAll [(f, f'), (a, a')]
           else matchFail loc
  -- Alternatives are okay as long as all corresponding alternatives are okay
  getMatch (IAlternative _ _ as) (IAlternative _ _ as')
      = matchAll (zip as as')
  -- TODO: IType, IAs (Q: how do as patterns work in 'with'???)
  getMatch pat spec = matchFail (getAnnot pat)

  matchAll : List (RawImp annot, RawImp annot) ->
             Core annot (List (String, RawImp annot))
  matchAll [] = pure []
  matchAll ((x, y) :: ms)
      = do matches <- matchAll ms
           mxy <- getMatch x y
           mergeMatches (mxy ++ matches)

  mergeMatches : List (String, RawImp annot) ->
                 Core annot (List (String, RawImp annot))
  mergeMatches [] = pure []
  mergeMatches ((n, tm) :: rest)
      = do rest' <- mergeMatches rest
           case lookup n rest' of
                Nothing => pure ((n, tm) :: rest')
                Just tm' =>
                   do getMatch tm tm' -- just need to know it succeeds
                      mergeMatches rest

