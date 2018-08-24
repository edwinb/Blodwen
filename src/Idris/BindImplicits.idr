module Idris.BindImplicits

import Core.TT
import TTImp.TTImp
import TTImp.Utils

%default covering

getUnique : List String -> String -> String
getUnique xs x = if x `elem` xs then getUnique xs (x ++ "'") else x

-- Rename the IBindVars in a term. Anything which appears in the list 'renames'
-- should be renamed, to something which is *not* in the list 'used'
export
renameIBinds : (renames : List String) -> 
               (used : List String) -> 
               RawImp annot -> RawImp annot
renameIBinds rs us (IPi fc c p (Just (UN n)) ty sc)
    = if n `elem` rs 
         then let n' = getUnique (rs ++ us) n
                  sc' = substNames (map UN (filter (/= n) us)) 
                                   [(UN n, IVar fc (UN n'))] sc in
              IPi fc c p (Just (UN n')) (renameIBinds rs us ty) 
                         -- No need to rename from here!
                         (renameIBinds rs (n' :: us) sc')
         else IPi fc c p (Just (UN n)) (renameIBinds rs us ty) 
                         (renameIBinds rs us sc)
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
renameIBinds rs us (IMustUnify fc r pat)
    = IMustUnify fc r (renameIBinds rs us pat)
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
doBind ns (IMustUnify fc r pat)
    = IMustUnify fc r (doBind ns pat)
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
