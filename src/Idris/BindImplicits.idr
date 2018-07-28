module Idris.BindImplicits

import Core.TT
import TTImp.TTImp

%default covering

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
findBindableNames arg env used (IAlternative fc u alts)
    = concatMap (findBindableNames arg env used) alts
-- We've skipped case, let and local - rather than guess where the
-- name should be bound, leave it to the programmer
findBindableNames arg env used tm = []

export
findIBinds : RawImp annot -> List String
findIBinds (IPi fc rig p mn aty retty)
    = findIBinds aty ++ findIBinds retty
findIBinds (ILam fc rig p n aty sc)
    = findIBinds aty ++ findIBinds sc
findIBinds (IApp fc fn av)
    = findIBinds fn ++ findIBinds av
findIBinds (IImplicitApp fc fn n av)
    = findIBinds fn ++ findIBinds av
findIBinds (IAs fc n pat)
    = findIBinds pat
findIBinds (IAlternative fc u alts)
    = concatMap findIBinds alts
findIBinds (IBindVar _ n) = [n]
-- We've skipped lambda, case, let and local - rather than guess where the
-- name should be bound, leave it to the programmer
findIBinds tm = []

-- Rename the IBindVars in a term. Anything which appears in the list 'renames'
-- should be renamed, to something which is *not* in the list 'used'
export
renameIBinds : (renames : List String) -> 
               (used : List String) -> 
               RawImp annot -> RawImp annot
renameIBinds rs us (IPi fc c p n ty sc)
    = IPi fc c p n (renameIBinds rs us ty) (renameIBinds rs us sc)
renameIBinds rs us (ILam fc c p n ty sc)
    = ILam fc c p n (renameIBinds rs us ty) (renameIBinds rs us sc)
renameIBinds rs us (IApp fc fn arg)
    = IApp fc (renameIBinds rs us fn) (renameIBinds rs us arg)
renameIBinds rs us (IImplicitApp fc fn n arg)
    = IImplicitApp fc (renameIBinds rs us fn) n (renameIBinds rs us arg)
renameIBinds rs us (IAs fc n pat)
    = IAs fc n (renameIBinds rs us pat)
renameIBinds rs us (IAlternative fc u alts)
    = IAlternative fc u (map (renameIBinds rs us) alts)
renameIBinds rs us (IBindVar fc n)
    = if n `elem` rs
         then IBindVar fc (getUnique (rs ++ us) n)
         else IBindVar fc n
renameIBinds rs us tm = tm

export
doBind : List (String, String) -> RawImp annot -> RawImp annot
doBind [] tm = tm
doBind ns (IVar fc (UN n))
    = maybe (IVar fc (UN n))
            (\n' => IBindVar fc n')
            (lookup n ns)
doBind ns (IPi fc rig p mn aty retty)
    = let ns' = case mn of
                     Just (UN n) => filter (\x => fst x /= n) ns
                     _ => ns in
          IPi fc rig p mn (doBind ns' aty) (doBind ns' retty)
doBind ns (ILam fc rig p mn aty sc)
    = let ns' = case mn of
                     Just (UN n) => filter (\x => fst x /= n) ns
                     _ => ns in
          ILam fc rig p mn (doBind ns' aty) (doBind ns' sc)
doBind ns (IApp fc fn av)
    = IApp fc (doBind ns fn) (doBind ns av)
doBind ns (IImplicitApp fc fn n av)
    = IImplicitApp fc (doBind ns fn) n (doBind ns av)
doBind ns (IAs fc n pat)
    = IAs fc n (doBind ns pat)
doBind ns (IAlternative fc u alts)
    = IAlternative fc u (map (doBind ns) alts)
doBind ns tm = tm

export
bindNames : (arg : Bool) -> RawImp annot -> (List Name, RawImp annot)
bindNames arg tm
    = let ns = nub (findBindableNames arg [] [] tm) in
          (map UN (map snd ns), doBind ns tm)

export
bindTypeNames : List Name -> RawImp annot -> RawImp annot
bindTypeNames env tm
    = let ns = nub (findBindableNames True env [] tm) in
          doBind ns tm

export
bindTypeNamesUsed : List String -> List Name -> RawImp annot -> RawImp annot
bindTypeNamesUsed used env tm
    = let ns = nub (findBindableNames True env used tm) in
          doBind ns tm

export
piBindNames : annot -> List Name -> RawImp annot -> RawImp annot
piBindNames loc env tm
    = let ns = nub (findBindableNames True env [] tm) in
          piBind (map fst ns) tm
  where
    piBind : List String -> RawImp annot -> RawImp annot
    piBind [] ty = ty
    piBind (n :: ns) ty 
       = IPi loc Rig0 Implicit (Just (UN n)) (Implicit loc) (piBind ns ty)
