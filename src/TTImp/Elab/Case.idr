module TTImp.Elab.Case

import TTImp.TTImp
import TTImp.Elab.Ambiguity
import TTImp.Elab.Delayed
import TTImp.Elab.Rewrite
import public TTImp.Elab.State
import TTImp.Reflect

import Core.AutoSearch
import Core.CaseTree
import Core.Context
import Core.Metadata
import Core.Normalise
import Core.Reflect
import Core.TT
import Core.Typecheck
import Core.Unify

import Data.List
import Data.List.Views

%default covering

export
caseBlock : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            {auto m : Ref Meta (Metadata annot)} ->
            Reflect annot =>
            RigCount -> Elaborator annot ->
            ElabInfo annot -> annot -> Env Term vars -> NestedNames vars -> 
            RawImp annot -> -- original scrutinee
            Term vars -> -- checked scrutinee
            Term vars -> -- its type
            RigCount -> -- its multiplicity
            List (ImpClause annot) -> ExpType (Term vars) ->
            Core annot (Term vars, Term vars)
caseBlock {vars} {c} {u} {i} {m} rigc process elabinfo loc env nest 
          scr scrtm_in scrty caseRig alts expected
    = do -- If there's any delayed ambiguities in the scrutinee, try to resolve
         -- them now
         scrtm <- handle (retryDelayedIn env loc scrtm_in)
                         (\err => if ambiguous err 
                                     then throw err
                                     else pure scrtm_in)

         gam <- get Ctxt
         log 2 $ "Case scrutinee: " ++ show caseRig ++ " " ++ 
                  show scrtm ++ " : " ++ show (normaliseHoles gam env scrty)
         scrn <- genName "scr"
         est <- get EST
         casen <- genCaseName (defining est)
         log 5 $ "Names used elsewhere: " ++ show (map fst (linearUsed est))

         -- Update environment so that linear bindings which aren't in
         -- 'usedNs' have multiplicity 0 in the case type
         let env = updateMults (linearUsed est) env
         -- If there's holes, we don't know whether or not locals have been used,
         -- so set any to multiplicity zero if the name doesn't appear in the
         -- case block
         -- FIXME: This isn't quite right, because the usage in the alts might
         -- be at 0 multiplicity, or could occur in an implicit, but it's a
         -- sound approximation for the moment (it will at least not lead to
         -- code typechecking which shouldn't!) It would be better if linearity
         -- checking was aware of case blocks.
         let env = case holesMade est of
                        [] => env
                        _ => setToZero (usedInAlts alts) env

         -- The 'pre_env' is the environment we apply any local (nested)
         -- names to. Here *all* the names have multiplicity 0 (we're
         -- going to abstract over them all again, in case the case block
         -- does any refining of their types/values)
         let pre_env = mkLocalEnv env

         defs <- get Ctxt
         -- To build the type, we abstract over the whole environment (so that
         -- we can use the nested names which might use that environment) and the
         -- part of the environment which is not the outer environment (so that we
         -- can dependent pattern match on parts of it). "smaller" is the outer
         -- environment, taken from the elaboration state, also removing
         -- things we can't match on and nothing depends on
         let (svars ** smaller) = shrinkEnv defs (subEnv est) [] [] env
         -- if the scrutinee is ones of the arguments in 'env' we should
         -- split on that, rather than adding it as a new argument
         let splitOn = findScrutinee env smaller scr
         
         caseretty <- case expected of
                           FnType [] ty => pure ty
                           _ =>
                              do t <- addHole loc env TType "ty"
                                 log 10 $ "Invented hole for case type " ++ show t
                                 pure (mkConstantApp t env)

         let casefnty = abstractOver env $
                          absOthers {done = []} (allow splitOn env) smaller 
                            (maybe (Bind scrn (Pi caseRig Explicit scrty) 
                                       (weaken caseretty))
                                   (const caseretty) splitOn)

         log 10 $ "Env: " ++ show (length vars) ++ " " ++ show vars
         log 10 $ "Outer env: " ++ show (outerEnv est)
         log 10 $ "Shrunk env: " ++ show svars
         log 2 $ "Case function type: " ++ show casen ++ " : " ++ show casefnty

         addDef casen (newDef [] casefnty Private None)
         setFlag loc casen Inline

         let alts' = map (updateClause casen splitOn env smaller) alts
         log 2 $ "Generated alts: " ++ show alts'
         log 2 $ "From: " ++ show alts
         log 5 $ "Nested: " ++ show (mkConstantAppFull casen pre_env)

         let nest' = record { names $= ((casen, (casen, 
                                  (mkConstantAppFull casen pre_env))) ::) } 
                            nest
         process c u i m True pre_env nest' (IDef loc casen alts')

         let applyEnv = applyToOthers (mkConstantAppFull casen env) env smaller
         pure (maybe (App applyEnv scrtm) (const applyEnv) splitOn, 
               caseretty)
  where
    findScrutinee : Env Term vs -> SubVars vs' vs ->
                    RawImp annot -> Maybe (x ** Elem x vs)
    findScrutinee {vs = n' :: _} (b :: bs) (DropCons p) (IVar loc' n)
        = if n' == n && notLet b
             then Just (n' ** Here)
             else do (_ ** p) <- findScrutinee bs p (IVar loc' n)
                     Just (_ ** There p)
      where
        notLet : Binder t -> Bool
        notLet (Let _ _ _) = False
        notLet _ = True
    findScrutinee (b :: bs) (KeepCons p) (IVar loc' n)
        = do (_ ** p) <- findScrutinee bs p (IVar loc' n)
             Just (_ ** There p)
    findScrutinee _ _ _ = Nothing

    dropHere : List (x ** Elem x (v :: vs)) -> List (x ** Elem x vs)
    dropHere [] = []
    dropHere ((_ ** Here) :: vs) = dropHere vs
    dropHere ((_ ** There p) :: vs) = (_ ** p) :: dropHere vs

    merge : {vs : List Name} ->
            List (x ** Elem x vs) -> List (x ** Elem x vs) -> List (x ** Elem x vs)
    merge [] xs = xs
    merge ((_ ** v) :: vs) xs
        = merge vs ((_ ** v) :: filter (\p => not (sameVar v (DPair.snd p))) xs)

    -- Extend the list of variables we need in the environment so far, removing
    -- duplicates
    extendNeeded : Binder (Term vs) -> 
                   Env Term vs -> List (x ** Elem x vs) ->
                   List (x ** Elem x vs)
    extendNeeded (Let c ty val) env needed
        = merge (findUsedLocs env ty) (merge (findUsedLocs env val) needed)
    extendNeeded (PLet c ty val) env needed
        = merge (findUsedLocs env ty) (merge (findUsedLocs env val) needed)
    extendNeeded b env needed
        = merge (findUsedLocs env (binderType b)) needed

    isNeeded : Elem x vs -> List (y ** Elem y vs) -> Bool
    isNeeded x [] = False
    isNeeded x ((_ ** y) :: xs) = sameVar x y || isNeeded x xs

    -- Shrink the environment so that any generated lambdas are not
    -- included.
    -- Here, 'Keep' means keep it in the outer environment, i.e. not needed
    -- for the case block. So, if it's already in the SubVars set, keep it,
    -- if it's not in the SubVars, keep it if it's a non-user name and
    -- doesn't appear in any types later in the environment
    -- (Yes, this is the opposite of what might seem natural, but we're
    -- starting from the 'outerEnv' which is the fragment of the environment
    -- used for the outer scope)
    shrinkEnv : Defs -> SubVars outer vs -> List (x ** Elem x vs) ->
                (done : List Name) ->
                Env Term vs ->
                (outer' ** SubVars outer' vs)
    shrinkEnv defs SubRefl needed done env = (_ ** SubRefl) -- keep them all
    -- usable name, so drop from the outer environment
    shrinkEnv {vs = UN n :: _} defs (DropCons p) needed done (b :: env) 
        = let (_ ** p') = shrinkEnv defs p 
                            (extendNeeded (map (normaliseHoles defs env) b) 
                                          env (dropHere needed)) 
                                          (UN n :: done) env in
              -- if shadowed and not needed, keep in the outer env
              if (UN n `elem` done) && not (isNeeded Here needed)
                 then (_ ** KeepCons p')
                 else (_ ** DropCons p')
    shrinkEnv {vs = n :: _} defs (DropCons p) needed done (b :: env)
        = let (_ ** p') = shrinkEnv defs p 
                            (extendNeeded (map (normaliseHoles defs env) b) 
                                          env (dropHere needed)) 
                                          (n :: done) env in
              if isNeeded Here needed || notLam b
                 then (_ ** DropCons p') else (_ ** KeepCons p')
      where
        notLam : Binder t -> Bool
        notLam (Lam _ _ _) = False
        notLam _ = True
    shrinkEnv {vs = n :: _} defs (KeepCons p) needed done (b :: env) 
        = let (_ ** p') = shrinkEnv defs p 
                            (extendNeeded (map (normaliseHoles defs env) b)
                                          env (dropHere needed)) 
                                          (n :: done) env in
              (_ ** KeepCons p') -- still keep it

    -- Is every occurence of the given variable name in a parameter
    -- position? 'ppos' says whether we are checking at a parameter
    -- position.
    asParam : Gamma -> (ppos : Bool) -> Elem v vs -> Term vs -> Bool
    asParam gam ppos var (Bind x (Let _ val ty) sc)
        = asParam gam False var val && asParam gam False var ty && 
          asParam gam ppos (There var) sc
    asParam gam ppos var (Bind x b sc)
        = asParam gam False var (binderType b) && 
          asParam gam ppos (There var) sc
    asParam gam ppos var tm with (unapply tm)
      asParam gam ppos var (apply (Local r x) []) | ArgsList
          = if sameVar var x then ppos else True
      asParam gam ppos var (apply (Ref nt n) args) | ArgsList
          = case lookupDefExact n gam of
                 Just (TCon _ _ ps _ _)
                   => asParamArgs gam var 0 ps args
                 _ => all (asParam gam False var) args
        where
          asParamArgs : Gamma -> Elem v vs -> Nat -> List Nat ->
                        List (Term vs) -> Bool
          asParamArgs gam var n ns [] = True
          asParamArgs gam var n ns (t :: ts) 
             = asParam gam (n `elem` ns) var t &&
               asParamArgs gam var (1 + n) ns ts
      asParam gam ppos var (apply f []) | ArgsList = True
      asParam gam ppos var (apply f args) | ArgsList 
          = all (asParam gam False var) args

    -- Drop names from the SubVars list which are *only* used in a
    -- parameter position in the term
    dropParams : Gamma -> Env Term vs -> SubVars vs' vs -> Term vs ->
                 (vs'' ** SubVars vs'' vs)
    dropParams gam [] sub tm = ([] ** SubRefl)
    dropParams gam (b :: env) SubRefl tm 
       = let (_ ** sub') = dropParams gam env SubRefl (subst Erased tm) in
             if asParam gam False Here tm
                then (_ ** DropCons sub')
                else (_ ** KeepCons sub')
    dropParams gam (b :: env) (DropCons p) tm
       = let (_ ** sub') = dropParams gam env p (subst Erased tm) in
             (_ ** DropCons sub')
    dropParams gam (b :: env) (KeepCons p) tm
       = let (_ ** sub') = dropParams gam env p (subst Erased tm) in
             if asParam gam False Here tm
                then (_ ** DropCons sub')
                else (_ ** KeepCons sub')

    toRig0 : Elem x vs -> Env Term vs -> Env Term vs
    toRig0 Here (b :: bs) = setMultiplicity b Rig0 :: bs
    toRig0 (There p) (b :: bs) = b :: toRig0 p bs

    toRig1 : Elem x vs -> Env Term vs -> Env Term vs
    toRig1 Here (b :: bs) 
        = if multiplicity b == Rig0
             then setMultiplicity b Rig1 :: bs
             else b :: bs
    toRig1 (There p) (b :: bs) = b :: toRig1 p bs

    -- If the name is used elsewhere, update its multiplicity so it's
    -- not required to be used in the case block
    updateMults : List (x ** Elem x vs) -> Env Term vs -> Env Term vs
    updateMults [] env = env
    updateMults ((_ ** p) :: us) env = updateMults us (toRig0 p env)

    allow : Maybe (x ** Elem x vs) -> Env Term vs -> Env Term vs
    allow Nothing env = env
    allow (Just (_ ** p)) env = toRig1 p env

    setToZero : List Name -> Env Term vs -> Env Term vs
    setToZero ns [] = []
    setToZero ns ((::) {x} b env)
        = case multiplicity b of
               Rig1 => if not (x `elem` ns)
                          then setMultiplicity b Rig0 :: setToZero ns env
                          else b :: setToZero ns env
               _ => b :: setToZero ns env

    mkLocalEnv : Env Term vs -> Env Term vs
    mkLocalEnv [] = []
    mkLocalEnv (b :: bs) 
        = let b' = if multiplicity b == Rig1
                      then setMultiplicity b Rig0
                      else b in
              b' :: mkLocalEnv bs

    export
    abstractOver : Env Term vs -> (tm : Term vs) -> ClosedTerm
    abstractOver [] tm = tm
    abstractOver (b :: env) tm 
        = let c = case multiplicity b of
                       Rig1 => Rig0
                       r => r in
          abstractOver env (Bind _ 
                (Pi c Explicit (binderType b)) tm)


    canBindName : Name -> List Name -> Maybe Name
    canBindName n@(UN _) vs
       = if n `elem` vs then Nothing else Just n
    canBindName _ vs = Nothing

    addEnv : Env Term vs -> SubVars vs' vs -> List Name -> 
             (List (Maybe (RawImp annot)), List Name)
    addEnv [] sub used = ([], used)
    -- Skip the let bindings, they were let bound in the case function type
    addEnv (Let _ _ _ :: bs) SubRefl used 
        = let (rest, used') = addEnv bs SubRefl used in
              (Nothing :: rest, used')
    addEnv (Let _ _ _ :: bs) (DropCons p) used 
        = let (rest, used') = addEnv bs p used in
              (Nothing :: rest, used')
    addEnv {vs = v :: vs} (b :: bs) SubRefl used
        = let (rest, used') = addEnv bs SubRefl used in
              (Nothing :: rest, used')
    addEnv (b :: bs) (KeepCons p) used
        = let (rest, used') = addEnv bs p used in
              (Nothing :: rest, used')
    addEnv {vs = v :: vs} (b :: bs) (DropCons p) used
        = let (rest, used') = addEnv bs p used in
              case canBindName v used' of
                   Just n => (Just (IAs loc n (Implicit loc)) :: rest, n :: used')
                   _ => (Just (Implicit loc) :: rest, used')

    -- Names used in the pattern we're matching on, so don't bind them
    -- in the generated case block
    usedIn : RawImp annot -> List Name
    usedIn (IBindVar _ n) = [UN n]
    usedIn (IApp _ f a) = usedIn f ++ usedIn a
    usedIn (IAs _ n a) = n :: usedIn a
    usedIn _ = []

    -- Replace a variable in the argument list; if the reference is to
    -- a variable kept in the outer environment (therefore not an argument
    -- in the list) don't consume it
    replace : Elem x vs -> RawImp annot -> List (Maybe (RawImp annot)) ->
              List (RawImp annot)
    replace Here lhs (_ :: xs) = lhs :: mapMaybe id xs
    replace (There p) lhs (Nothing :: xs) 
        = replace p lhs xs
    replace (There p) lhs (Just x :: xs) 
        = x :: replace p lhs xs
    replace _ _ xs = mapMaybe id xs

    mkSplit : Maybe (x ** Elem x vs) -> 
              RawImp annot -> List (Maybe (RawImp annot)) -> 
              List (RawImp annot)
    mkSplit Nothing lhs args = reverse (lhs :: mapMaybe id args)
    mkSplit (Just (_ ** prf)) lhs args
        = reverse (replace prf lhs args)

    updateClause : Name -> Maybe (x ** Elem x vars) ->
                   Env Term vars -> SubVars vs' vars ->
                   ImpClause annot -> ImpClause annot
    updateClause casen splitOn env sub (PatClause loc' lhs rhs)
        = let args = fst (addEnv env sub (usedIn lhs))
              args' = mkSplit splitOn lhs args in
              PatClause loc' (apply (IVar loc' casen) args') rhs
    updateClause casen splitOn env sub (ImpossibleClause loc' lhs)
        = let args = fst (addEnv env sub (usedIn lhs))
              args' = mkSplit splitOn lhs args in
              ImpossibleClause loc' (apply (IVar loc' casen) args')
  
