module Idris.BindImplicits

import Core.TT
import TTImp.TTImp

lowerFirst : String -> Bool
lowerFirst "" = False
lowerFirst str = assert_total (isLower (strHead str))

-- Bind lower case names in argument position
-- Don't go under lambda, case let, or local bindings, or IAlternative
export
findBindableNames : (arg : Bool) -> List Name -> RawImp annot -> List String
findBindableNames True env (IVar fc (UN n))
    = if not (UN n `elem` env) && lowerFirst n
         then [n]
         else []
findBindableNames arg env (IPi fc rig p mn aty retty)
    = let env' = case mn of
                      Nothing => env
                      Just n => n :: env in
          findBindableNames True env' aty ++
          findBindableNames True env' retty
findBindableNames arg env (IApp fc fn av)
    = findBindableNames False env fn ++ findBindableNames True env av
findBindableNames arg env (IImplicitApp fc fn n av)
    = findBindableNames False env fn ++ findBindableNames True env av
findBindableNames arg env (IAs fc n pat)
    = findBindableNames arg env pat
findBindableNames arg env (IAlternative fc u alts)
    = concatMap (findBindableNames arg env) alts
-- We've skipped lambda, case, let and local - rather than guess where the
-- name should be bound, leave it to the programmer
findBindableNames arg env tm = []

export
doBind : List String -> RawImp annot -> RawImp annot
doBind [] tm = tm
doBind ns (IVar fc (UN n))
    = if n `elem` ns
         then IBindVar fc n
         else IVar fc (UN n)
doBind ns (IPi fc rig p mn aty retty)
    = let ns' = case mn of
                     Just (UN n) => ns \\ [n]
                     _ => ns in
          IPi fc rig p mn (doBind ns' aty) (doBind ns' retty)
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
    = let ns = nub (findBindableNames arg [] tm) in
          (map UN ns, doBind ns tm)

export
bindTypeNames : List Name -> RawImp annot -> RawImp annot
bindTypeNames env tm
    = let ns = nub (findBindableNames True env tm) in
          doBind ns tm

export
piBindNames : annot -> List Name -> RawImp annot -> RawImp annot
piBindNames loc env tm
    = let ns = nub (findBindableNames True env tm) in
          piBind ns tm
  where
    piBind : List String -> RawImp annot -> RawImp annot
    piBind [] ty = ty
    piBind (n :: ns) ty 
       = IPi loc Rig0 Implicit (Just (UN n)) (Implicit loc) (piBind ns ty)
