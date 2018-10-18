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

