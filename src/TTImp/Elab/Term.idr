module TTImp.Elab.Term

import TTImp.TTImp
import public TTImp.Elab.State
import Core.AutoSearch
import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT
import Core.Typecheck
import Core.Unify

import Data.List
import Data.List.Views

%default covering

-- If the expected type has an implicit pi, elaborate with leading
-- implicit lambdas (so at the moment, implicit lambdas can only be inserted
-- by the machine, not a programmer.)
insertImpLam : Env Term vars ->
               (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
               RawImp annot
insertImpLam env tm Nothing = tm
insertImpLam env tm (Just ty) = bindLam tm ty
  where
    bindLam : RawImp annot -> Term vars -> RawImp annot
    bindLam tm (Bind n (Pi c Implicit ty) sc)
        = let loc = getAnnot tm in
              ILam loc RigW Implicit n (Implicit loc) (bindLam tm sc)
    bindLam tm sc = tm

expandAmbigName : Defs -> Env Term vars -> NestedNames vars ->
                  RawImp annot -> 
                  List (annot, RawImp annot) -> RawImp annot -> 
                  Maybe (Term vars) -> RawImp annot
expandAmbigName defs env nest orig args (IVar loc x) exp
   = case lookup x (names nest) of
          Just _ => orig
          Nothing => 
            case defined x env of
                 Just _ => orig
                 Nothing => case lookupDefTyNameIn (currentNS defs) x 
                                                   (gamma defs) of
                                 [] => orig
                                 [(n, _)] => buildAlt (IVar loc n) args
                                 ns => IAlternative loc True
                                         (map (\n => buildAlt (IVar loc n) args) 
                                              (map fst ns))
  where
    buildAlt : RawImp annot -> List (annot, RawImp annot) -> RawImp annot
    buildAlt f [] = f
    buildAlt f ((loc', a) :: as) = buildAlt (IApp loc' f a) as
expandAmbigName defs env nest orig args (IApp loc f a) exp
   = expandAmbigName defs env nest orig ((loc, a) :: args) f exp
expandAmbigName defs env nest orig args _ _ = orig

-- Erase any forced arguments from a top level application
eraseForced : Gamma -> Term vars -> Term vars
eraseForced gam tm with (unapply tm)
  eraseForced gam (apply (Ref (DataCon t ar) n) args) | ArgsList 
      = case lookupDefExact n gam of
             Just (DCon _ _ forcedpos)
                  => apply (Ref (DataCon t ar) n) (dropPos 0 forcedpos args)
             _ => apply (Ref (DataCon t ar) n) args
    where
      dropPos : Nat -> List Nat -> List (Term vars) -> List (Term vars)
      dropPos i fs [] = []
      dropPos i fs (x :: xs)
          = if i `elem` fs then Erased :: dropPos (S i) fs xs
                           else x :: dropPos (S i) fs xs
  eraseForced gam (apply f args) | ArgsList = apply f args

bindRig : RigCount -> RigCount
bindRig Rig0 = Rig0
bindRig _ = Rig1

mutual
  export
  check : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
          {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
          RigCount ->
          Elaborator annot -> -- the elaborator for top level declarations
                              -- used for nested definitions
          ElabInfo annot -> -- elaboration parameters
          Env Term vars -> -- bound names (lambda, pi, let)
          NestedNames vars -> -- locally defined names (arising from nested top level
                              -- declarations)
          (term : RawImp annot) -> -- Term to elaborate
          (expected : Maybe (Term vars)) -> -- Expected type, if available
          Core annot (Term vars, Term vars) 
  check rigc process elabinfo env nest tm_in exp 
      = do gam <- get Ctxt
           let tm = expandAmbigName gam env nest tm_in [] tm_in exp
           let lazyTm = insertLazy gam tm (map (nf gam env) exp)
           case elabMode elabinfo of
               -- don't expand implicit lambda on LHS
               InLHS => checkImp rigc process elabinfo env nest lazyTm exp
               _ => let tm' = insertImpLam env lazyTm exp 
                        loc = getAnnot tm' in
                        case forceName gam of
                             Nothing => (checkImp rigc process elabinfo env nest tm' exp)
                             Just fn =>
                                let forcetm = IApp loc (IVar loc fn) tm' in
                                    insertForce 
                                      (checkImp rigc process elabinfo env nest tm' exp)
                                      (checkImp rigc process elabinfo env nest forcetm exp)

  delayError : Defs -> Error annot -> Bool
  delayError defs (CantConvert _ env x y) 
      = headDelay (nf defs env x) || headDelay (nf defs env y)
    where
      headDelay : NF vars -> Bool
      headDelay (NTCon n _ _ _) = isDelayType n defs
      headDelay _ = False
  delayError defs (WhenUnifying _ _ x y err) = delayError defs err
  delayError defs (InType _ _ err) = delayError defs err
  delayError defs (InCon _ _ err) = delayError defs err
  delayError defs (InLHS _ _ err) = delayError defs err
  delayError defs (InRHS _ _ err) = delayError defs err
  delayError _ _ = False

  insertForce : {auto c : Ref Ctxt Defs} -> 
                {auto u : Ref UST (UState annot)} ->
                {auto i : Ref ImpST (ImpState annot)} ->
                Core annot (Term vars, Term vars) ->
                Core annot (Term vars, Term vars) ->
                Core annot (Term vars, Term vars)
  insertForce elab forced
      = handle elab
               (\err => do defs <- get Ctxt
                           if delayError defs err then forced else throw err)

  concrete : Defs -> NF vars -> Bool
  concrete defs (NApp (NRef nt n) args)
      = case lookupDefExact n (gamma defs) of
             Just (Hole _ pvar) => pvar
             _ => False
  concrete defs _ = True

  insertLazy : Defs -> RawImp annot -> Maybe (NF vars) -> RawImp annot
  insertLazy defs tm@(IBindVar _ _) _ = tm
  -- If the expected type is "Delayed" and its arguments aren't holes,
  -- then we'll try inserting a "Delay"
  insertLazy defs tm (Just (NTCon n _ _ args))
      = case delayName defs of
             Nothing => tm
             Just delay =>
                if isDelayType n defs &&
                   not (explicitLazy defs (getFn tm)) &&
                   all (\x => concrete defs (evalClosure defs x)) args
                   then let loc = getAnnot tm in
                            IAlternative loc False 
                             [IApp loc (IVar loc delay) tm,
                              tm]
                   else tm
  insertLazy defs tm _ = tm

  checkImp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
             RigCount ->
             Elaborator annot ->
             ElabInfo annot ->
             Env Term vars -> NestedNames vars ->
             (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
             Core annot (Term vars, Term vars) 
  checkImp rigc process elabinfo env nest (IVar loc x) expected 
      = case lookup x (names nest) of
             Just (n', tm) =>
                  do gam <- get Ctxt
                     case lookupTyExact n' (gamma gam) of
                          Nothing => throw (UndefinedName loc n')
                          Just varty => 
                             do let tyenv = useVars (getArgs tm) (embed varty)
                                (ty_nf, imps) <- getImps rigc process loc env nest elabinfo (nf gam env tyenv) []
                                let ty = quote (noGam gam) env ty_nf
                                log 5 $ "Type of " ++ show n' ++ " : " ++ show ty
                                log 5 $ "Term: " ++ show (apply tm imps)
                                checkExp rigc process loc elabinfo env nest 
                                         (apply tm imps) ty expected
             _ => checkName rigc process elabinfo loc env nest x expected
    where
      useVars : List (Term vars) -> Term vars -> Term vars
      useVars [] sc = sc
      useVars (a :: as) (Bind n (Pi c _ ty) sc) 
           = Bind n (Let c a ty) (useVars (map weaken as) sc)
      useVars _ sc = sc -- Can't happen?
  checkImp rigc process elabinfo env nest (IPi loc rigp plicity Nothing ty retTy) expected 
      = do n <- genName "pi"
           checkPi rigc process elabinfo loc env nest rigp plicity (dropNS n) ty retTy expected
  checkImp rigc process elabinfo env nest (IPi loc rigp plicity (Just n) ty retTy) expected 
      = checkPi rigc process elabinfo loc env nest rigp plicity n ty retTy expected
  checkImp rigc process elabinfo env nest (ILam loc rigl plicity n ty scope) expected
      = checkLam (bindRig rigc) process elabinfo loc env nest rigl plicity n ty scope expected
  checkImp rigc process elabinfo env nest (ILet loc rigl n nTy nVal scope) expected 
      = checkLet (bindRig rigc) process elabinfo loc env nest rigl n nTy nVal scope expected
  checkImp rigc process elabinfo env nest (ICase loc scr alts) expected 
      = checkCase rigc process elabinfo loc env nest scr alts expected
  checkImp rigc process elabinfo env nest (ILocal loc nested scope) expected 
      = checkLocal rigc process elabinfo loc env nest nested scope expected
  checkImp rigc process elabinfo env nest (IApp loc fn arg) expected 
      = do -- Collect the implicits from the top level application first
           let (fn', args) = collectGivenImps fn
           let elabinfo' = addGivenImps elabinfo args
           log 10 $ "Implicits: " ++ show (implicitsGiven elabinfo')
           (restm, resty) <- checkApp rigc process elabinfo' loc env nest fn' arg expected
           -- Add any remaining implicits greedily
           gam <- get Ctxt
           (ty, imps) <- getImps rigc process loc env nest elabinfo' (nf gam env resty) []
           log 10 $ "Checked app " ++ show (restm, quote (noGam gam) env ty, imps)
           -- Check all of the implicits we collected have been used
           est <- get EST
           log 10 $ "Used: " ++ show (implicitsUsed est, map fst args)
           checkUsedImplicits loc (implicitsUsed est) (map fst args) (apply restm imps)
           case imps of
                [] => pure (restm, resty)
                _ => checkExp rigc process loc elabinfo env nest (apply restm imps) 
                              (quote (noGam gam) env ty) expected
  checkImp rigc process elabinfo env nest (IImplicitApp loc fn nm arg) expected 
      = do let (fn', args) = collectGivenImps fn
           let elabinfo' = addGivenImps elabinfo ((nm, arg) :: args)
           log 10 $ "IImplicits: " ++ show (implicitsGiven elabinfo')
           (restm, resty) <- check rigc process elabinfo' env nest fn' expected
           -- Add any remaining implicits greedily
           gam <- get Ctxt
           (ty, imps) <- getImps rigc process loc env nest elabinfo' (nf gam env resty) []
           log 10 $ "Checked app " ++ show (restm, quote (noGam gam) env ty, imps)
           -- Check all of the implicits we collected have been used
           est <- get EST
           log 10 $ "IUsed: " ++ show (implicitsUsed est, nm :: map fst args)
           checkUsedImplicits loc (implicitsUsed est) (nm :: map fst args) (apply restm imps)
           case imps of
                [] => pure (restm, resty)
                _ => checkExp rigc process loc elabinfo env nest (apply restm imps) 
                              (quote (noGam gam) env ty) expected
  checkImp rigc process elabinfo env nest (ISearch loc depth) Nothing
      = throw (InternalError "Trying to search for a term with an unknown type")
  checkImp rigc process elabinfo env nest (ISearch loc depth) (Just expected)
      = do n <- addSearchable loc env expected depth
           let umode = case elabMode elabinfo of
                            InLHS => InLHS
                            _ => InTerm
           -- try again to solve the holes, including the search we've just added.
           solveConstraints umode False
           pure (mkConstantApp n env, expected)
  checkImp rigc process elabinfo env nest (IAlternative loc uniq alts) expected
      = delayOnFailure loc env expected ambiguous $
          (do gam <- get Ctxt
              log 5 $ "Ambiguous elaboration " ++ show alts ++ 
                      "\nTarget type " ++ show (map (normaliseHoles gam env) expected)
              let tryall = if uniq then exactlyOne else anyOne 
              tryall loc (map (\t => 
                     checkImp rigc process elabinfo env nest t expected) alts))
    where
      ambiguous : Error annot -> Bool
      ambiguous (AmbiguousElab _ _) = True
      ambiguous (AmbiguousName _ _) = True
      ambiguous (InType _ _ err) = ambiguous err
      ambiguous (InCon _ _ err) = ambiguous err
      ambiguous (InLHS _ _ err) = ambiguous err
      ambiguous (InRHS _ _ err) = ambiguous err
      ambiguous _ = False
  checkImp rigc process elabinfo env nest (IPrimVal loc x) expected 
      = do (x', ty) <- infer loc env (RPrimVal x)
           checkExp rigc process loc elabinfo env nest x' ty expected
  checkImp rigc process elabinfo env nest (IType loc) exp
      = checkExp rigc process loc elabinfo env nest TType TType exp
  checkImp rigc process elabinfo env nest (IBindVar loc str) exp with (elabMode elabinfo)
    checkImp rigc process elabinfo env nest (IBindVar loc str) exp | InExpr
      = throw (BadImplicit loc str)
    checkImp rigc process elabinfo env nest (IBindVar loc str) Nothing | elabmode
        = do let n = PV str
             t <- addHole loc env TType
             let hty = mkConstantApp t env
             est <- get EST
             case lookup n (boundNames est) of
                  Nothing =>
                    do tm <- addBoundName loc n True env hty
                       put EST 
                           (record { boundNames $= ((n, (tm, hty)) ::),
                                     toBind $= ((n, (tm, hty)) ::) } est)
                       pure (tm, hty)
                  Just (tm, ty) =>
                       pure (tm, ty)
    checkImp rigc process elabinfo env nest (IBindVar loc str) (Just expected) | elabmode
        = do let n = PV str
             est <- get EST
             case lookup n (boundNames est) of
                  Nothing =>
                    do tm <- addBoundName loc n True env expected
                       log 5 $ "Added Bound implicit " ++ show (n, (tm, expected))
                       put EST 
                           (record { boundNames $= ((n, (tm, expected)) ::),
                                     toBind $= ((n, (tm, expected)) :: ) } est)
                       pure (tm, expected)
                  Just (tm, ty) =>
                       if repeatBindOK (dotted elabinfo) (elabMode elabinfo)
                          then checkExp rigc process loc elabinfo env nest tm ty (Just expected)
                          else throw (NonLinearPattern loc n)
      where
        repeatBindOK : Bool -> ElabMode -> Bool
        repeatBindOK False InLHS = False
        repeatBindOK _ _ = True
  checkImp rigc process elabinfo env nest (IMustUnify loc tm) (Just expected) with (elabMode elabinfo)
    checkImp rigc process elabinfo env nest (IMustUnify loc tm) (Just expected) | InLHS
      = do (wantedTm, wantedTy) <- checkImp rigc process 
                                            (record { dotted = True } elabinfo)
                                            env nest tm (Just expected)
           n <- addHole loc env expected
           gam <- getCtxt
           let tm = mkConstantApp n env
           addDot loc env wantedTm tm
           checkExp rigc process loc (record { elabMode= InExpr } elabinfo) 
                    env nest tm wantedTy (Just expected)
    checkImp rigc process elabinfo env nest (IMustUnify loc tm) (Just expected) | elabmode
        = throw (GenericMsg loc "Dot pattern not valid here")
  checkImp rigc process elabinfo env nest (IMustUnify loc tm) expected
      = throw (GenericMsg loc "Dot pattern not valid here")
  checkImp rigc process elabinfo env nest (IAs loc var tm) expected with (elabMode elabinfo)
    checkImp rigc process elabinfo env nest (IAs loc var tm) (Just expected) | InLHS
      = checkAs rigc process elabinfo loc env nest var tm expected
    checkImp rigc process elabinfo env nest (IAs loc var tm) expected | elabmode
        = throw (GenericMsg loc "@-pattern not valid here")
  checkImp rigc process elabinfo env nest (IHole loc n_in) Nothing
      = do t <- addHole loc env TType
           let hty = mkConstantApp t env
           n <- inCurrentNS (UN n_in)
           addNamedHole loc n False env hty
           pure (mkConstantApp n env, hty)
  checkImp rigc process elabinfo env nest (IHole loc n_in) (Just expected) 
      = do n <- inCurrentNS (UN n_in)
           addNamedHole loc n False env expected
           pure (mkConstantApp n env, expected)
  checkImp rigc process elabinfo env nest (Implicit loc) Nothing
      = do t <- addHole loc env TType
           let hty = mkConstantApp t env
           n <- addHole loc env hty
           pure (mkConstantApp n env, hty)
  checkImp rigc process elabinfo env nest (Implicit loc) (Just expected) 
      = case elabMode elabinfo of
             InLHS =>
                do hn <- genName "imp_pat"
                   -- Add as a pattern variable, but let it unify with other
                   -- things, hence 'False' as an argument to addBoundName
                   tm <- addBoundName loc hn False env expected
                   est <- get EST
                   put EST (record { boundNames $= ((hn, (tm, expected)) :: ),
                                     toBind $= ((hn, (tm, expected)) :: ) } est)
                   pure (tm, expected)
             _ =>
                do n <- addHole loc env expected
                   pure (mkConstantApp n env, expected)

  addGivenImps : ElabInfo annot -> List (Name, RawImp annot) -> ElabInfo annot
  addGivenImps elabinfo ns = record { implicitsGiven $= (ns ++) } elabinfo

  -- Check a name. At this point, we've already established that it's not
  -- one of the local definitions, so it either must be a local variable or
  -- a globally defined name
  checkName : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
              {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
              RigCount -> Elaborator annot -> ElabInfo annot -> annot -> Env Term vars -> 
              NestedNames vars -> Name -> Maybe (Term vars) ->
              Core annot (Term vars, Term vars)
  checkName {vars} rigc process elabinfo loc env nest x expected 
      = do gam <- get Ctxt
           case defined x env of
             Just (rigb, lv) => 
                 do rigSafe rigb rigc
                    let varty = binderType (getBinder lv env) 
                    (ty, imps) <- getImps rigc process loc env nest elabinfo (nf gam env varty) []
                    checkExp rigc process loc elabinfo env nest (apply (Local lv) imps)
                            (quote (noGam gam) env ty) expected
             Nothing =>
                 do nspace <- getNS
                    case lookupDefTyNameIn nspace x (gamma gam) of
                         [] => throw $ UndefinedName loc x
                         [(fullname, def, ty)] => 
                              resolveRef fullname def gam (embed ty)
                         ns => exactlyOne loc (map (\ (n, def, ty) =>
                                       resolveRef n def gam (embed ty)) ns)
    where
      rigSafe : RigCount -> RigCount -> Core annot ()
      rigSafe Rig1 RigW = throw (LinearMisuse loc x Rig1 RigW)
      rigSafe Rig0 RigW = throw (LinearMisuse loc x Rig0 RigW)
      rigSafe Rig0 Rig1 = throw (LinearMisuse loc x Rig0 Rig1)
      rigSafe _ _ = pure ()

      defOK : Bool -> ElabMode -> NameType -> Bool
      defOK False InLHS (DataCon _ _) = True
      defOK False InLHS _ = False
      defOK _ _ _ = True

      checkVisibleNS : Name -> Core annot ()
      checkVisibleNS (NS ns x)
          = if !(isVisible ns)
               then pure ()
               else do defs <- get Ctxt
                       throw $ InvisibleName loc (NS ns x)
      checkVisibleNS _ = pure ()

      resolveRef : Name -> Def -> Defs -> Term vars -> 
                   Core annot (Term vars, Term vars)
      resolveRef n def gam varty
          = do checkVisibleNS n
               let nt : NameType 
                        = case def of
                             PMDef _ _ _ => Func
                             DCon tag arity _ => DataCon tag arity
                             TCon tag arity _ _ => TyCon tag arity
                             _ => Func
               (ty, imps) <- getImps rigc process loc env nest elabinfo (nf gam env varty) []
               if topLevel elabinfo ||
                    defOK (dotted elabinfo) (elabMode elabinfo) nt
                  then checkExp rigc process loc elabinfo env nest (apply (Ref nt n) imps) 
                            (quote (noGam gam) env ty) expected
                  else throw (BadPattern loc n)

  checkCase : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
              {auto e : Ref EST (EState vars)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              RigCount -> Elaborator annot ->
              ElabInfo annot -> annot -> Env Term vars -> NestedNames vars -> 
              RawImp annot -> List (ImpClause annot) ->
              Maybe (Term vars) ->
              Core annot (Term vars, Term vars)
  checkCase {c} {u} {i} rigc process elabinfo loc env nest scr alts expected
      = do (scrtm, scrty) <- check rigc process elabinfo env nest scr Nothing
           log 5 $ "Case scrutinee: " ++ show scrtm ++ " : " ++ show scrty
           scrn <- genName "scr"
           est <- get EST
           casen <- genCaseName (defining est)
           let usedNs = usedInAlts alts

           log 6 $ "Names used in case block: " ++ show usedNs

           -- Update environment so that linear bindings which aren't in
           -- 'usedNs' have multiplicity 0 in the case type
           let env = updateMults usedNs env

           gam <- getCtxt
           let (_ ** smallerIn) = findSubEnv env scrty
           let (_ ** smaller) = dropParams gam env smallerIn scrty
           
           caseretty <- case expected of
                             Just ty => pure ty
                             Nothing =>
                                do t <- addHole loc env TType
                                   pure (mkConstantApp t env)
           let casefnty = abstractEnvType env $
                            absSmaller {done = []} env smaller 
                              (Bind scrn (Pi RigW Explicit scrty) 
                                         (weaken caseretty))

           log 3 $ "Case function type: " ++ show casen ++ " : " ++ show casefnty

           addDef casen (newDef casefnty Private None)

           let alts' = map (updateClause casen env smaller) alts
           log 5 $ "Generated alts: " ++ show alts'

           let nest' = record { names $= ((casen, (casen, 
                                    (mkConstantApp casen env))) ::) } nest
           process c u i env nest' (IDef loc casen alts')

           pure (App (applyToSub (mkConstantApp casen env) env smaller) 
                     scrtm, caseretty)
    where
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
        asParam gam ppos var (apply (Local x) []) | ArgsList
            = if sameVar var x then ppos else True
        asParam gam ppos var (apply (Ref nt n) args) | ArgsList
            = case lookupDefExact n gam of
                   Just (TCon _ _ ps _)
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

      asBind : Name -> annot -> RawImp annot -> RawImp annot
      asBind (UN n) ann tm = IAs ann n tm
      asBind _ ann tm = tm

      updateMults : List Name -> Env Term vs -> Env Term vs
      updateMults ns [] = []
      updateMults ns ((::) {x} b bs)
         -- if it's not used in the case block, it should have 0 multiplicity
         -- in the case block's type, otherwise leave it alone
         = if multiplicity b == Rig1 && not (x `elem` ns)
              then setMultiplicity b Rig0 :: updateMults (filter (/=x) ns) bs
              else b :: updateMults (filter (/=x) ns) bs

      addEnv : Env Term vs -> SubVars vs' vs -> List Name -> List (RawImp annot)
      addEnv [] sub used = []
      addEnv (b :: bs) SubRefl used
          = Implicit loc :: addEnv bs SubRefl used
      addEnv (b :: bs) (DropCons p) used
          = addEnv bs p used
      addEnv (b :: bs) (KeepCons p) used
          = Implicit loc :: addEnv bs p used

      -- Names used in the pattern we're matching on, so don't bind them
      -- in the generated case block
      usedIn : RawImp annot -> List Name
      usedIn (IBindVar _ n) = [UN n]
      usedIn (IApp _ f a) = usedIn f ++ usedIn a
      usedIn (IAs _ n a) = UN n :: usedIn a
      usedIn _ = []

      updateClause : Name -> Env Term vars -> SubVars vs' vars ->
                     ImpClause annot -> ImpClause annot
      updateClause casen env sub (PatClause loc' lhs rhs)
          = let args = addEnv env sub (usedIn lhs) in
                PatClause loc' (apply (IVar loc casen) (reverse (lhs :: args))) rhs
      updateClause casen env sub (ImpossibleClause loc' lhs)
          = let args = addEnv env sub (usedIn lhs) in
                ImpossibleClause loc' (apply (IVar loc casen) (reverse (lhs :: args)))
  
  checkLocal : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
               {auto e : Ref EST (EState vars)} ->
               {auto i : Ref ImpST (ImpState annot)} ->
               RigCount -> Elaborator annot ->
               ElabInfo annot -> annot -> Env Term vars -> NestedNames vars -> 
               List (ImpDecl annot) -> RawImp annot ->
               Maybe (Term vars) ->
               Core annot (Term vars, Term vars)
  checkLocal {vars} {c} {u} {i} rigc process elabinfo loc env nest nested scope expected
      = do let defNames = definedInBlock nested
           est <- get EST
           let f = defining est
           let nest' = record { names $= ((map (applyEnv f) defNames) ++) } nest
           let env' = dropLinear env
           traverse (process c u i env' nest') (map (updateName nest') nested)
           checkImp rigc process elabinfo env nest' scope expected
    where
      -- For the local definitions, don't allow access to linear things
      -- unless they're explicitly passed.
      -- This is because, at the moment, we don't have any mechanism of
      -- ensuring the nested definition is used exactly once
      dropLinear : Env Term vs -> Env Term vs
      dropLinear [] = []
      dropLinear (b :: bs) 
          = if multiplicity b == Rig1
               then setMultiplicity b Rig0 :: dropLinear bs
               else b :: dropLinear bs

      applyEnv : Name -> Name -> (Name, (Name, Term vars))
      applyEnv outer inner = (inner, (GN (Nested outer inner), 
                                      mkConstantApp (GN (Nested outer inner)) env))

      -- Update the names in the declarations to the new 'nested' names.
      -- When we encounter the names in elaboration, we'll update to an
      -- application of the nested name.
      newName : NestedNames vars -> Name -> Name
      newName nest n 
          = case lookup n (names nest) of
                 Just (n', _) => n'
                 _ => n

      updateTyName : NestedNames vars -> ImpTy annot -> ImpTy annot
      updateTyName nest (MkImpTy loc' n ty) = MkImpTy loc' (newName nest n) ty

      updateDataName : NestedNames vars -> ImpData annot -> ImpData annot
      updateDataName nest (MkImpData loc' n tycons dcons)
          = MkImpData loc' (newName nest n) tycons (map (updateTyName nest) dcons)

      updateName : NestedNames vars -> ImpDecl annot -> ImpDecl annot
      updateName nest (IClaim loc' vis ty) = IClaim loc' vis (updateTyName nest ty)
      updateName nest (IDef loc' n cs) = IDef loc' (newName nest n) cs
      updateName nest (IData loc' vis d) = IData loc' vis (updateDataName nest d)
      updateName nest i = i

  checkAs : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            RigCount -> Elaborator annot ->
            ElabInfo annot -> annot -> Env Term vars -> NestedNames vars -> 
            String -> (arg : RawImp annot) ->
            Term vars ->
            Core annot (Term vars, Term vars) 
  checkAs rigc process elabinfo loc env nest var tm expected
      = do let n = PV var
           (patTm, patTy) <- checkImp rigc process elabinfo env nest tm (Just expected)
           est <- get EST
           case lookup n (boundNames est) of
                Just (tm, ty) =>
                    throw (GenericMsg loc ("Name " ++ var ++ " already bound"))
                Nothing =>
                    do tm <- addBoundName loc n False env expected
                       log 5 $ "Added @ pattern name " ++ show (n, (tm, expected))
                       put EST
                           (record { boundNames $= ((n, (tm, expected)) ::),
                                     toBind $= ((n, (tm, expected)) ::),
                                     asVariables $= (n ::) } est)
                       gam <- get Ctxt
                       convert loc InLHS env (nf gam env patTm) (nf gam env tm)
                       pure (patTm, expected)

  checkApp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             RigCount -> Elaborator annot ->
             ElabInfo annot -> annot -> Env Term vars -> NestedNames vars -> 
             (fn : RawImp annot) -> (arg : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkApp rigc process elabinfo loc env nest fn arg expected
      = do (fntm, fnty) <- check rigc process elabinfo env nest fn Nothing
           gam <- get Ctxt
           case nf gam env fnty of
                NBind _ (Pi rigf _ ty) scdone =>
                  do impsUsed <- saveImps
                     let argRig = rigMult rigf rigc
                     -- Can't pattern match on arguments at Rig0
                     let arg' = case (elabMode elabinfo, arg, argRig) of
                                     (_, IBindVar _ _, _) => arg
                                     (_, Implicit _, _) => arg
                                     (InLHS, _, Rig0) => IMustUnify loc arg
                                     _ => arg
                     (argtm, argty) <- check (rigMult rigf rigc)
                                             process (record { implicitsGiven = [] } elabinfo)
                                             env nest arg' (Just (quote (noGam gam) env ty))
                     restoreImps impsUsed
                     let sc' = scdone (toClosure False env argtm)
                     gam <- get Ctxt
                     checkExp rigc process loc elabinfo env nest (App fntm argtm)
                                  (quote gam env sc') expected
                _ => 
                  do bn <- genName "aTy"
                     -- invent names for the argument and return types
                     log 5 $ "Inventing arg type for " ++ show (fn, fnty)
                     (expty, scty) <- inventFnType loc env bn
                     -- Check the argument type against the invented arg type
                     impsUsed <- saveImps
                     (argtm, argty) <- check rigc process (record { implicitsGiven = [] } elabinfo)
                                             env nest arg (Just expty)
                     restoreImps impsUsed
                     -- Check the type of 'fn' is an actual function type
                     gam <- get Ctxt
                     (fnchk, _) <-
                         checkExp rigc process loc elabinfo env nest fntm 
                                  (Bind bn (Pi RigW Explicit expty) scty) 
                                  (Just (quote gam env fnty))
                     checkExp rigc process loc elabinfo env nest (App fnchk argtm)
                                  (Bind bn (Let RigW argtm argty) scty) expected

  checkPi : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            RigCount -> Elaborator annot -> ElabInfo annot ->
            annot -> Env Term vars -> NestedNames vars -> RigCount -> PiInfo -> Name -> 
            (argty : RawImp annot) -> (retty : RawImp annot) ->
            Maybe (Term vars) ->
            Core annot (Term vars, Term vars) 
  checkPi rigc process elabinfo loc env nest rigf info n argty retty expected
      = do let top = topLevel elabinfo
           let impmode = implicitMode elabinfo
           let elabmode = elabMode elabinfo
           (tyv, tyt) <- check Rig0 process (record { topLevel = False } elabinfo) 
                               env nest argty (Just TType)
           let env' : Env Term (n :: _) = Pi RigW info tyv :: env
           est <- get EST
           
           tobind <- getToBind env
           let argImps = if top then tobind else []
           -- note the names as now being bound implicits, so we don't bind again
           setBound (map fst argImps)
           when top $ clearToBind 
           e' <- weakenedEState 
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} rigc process elabinfo env' (weaken nest') retty (Just TType)
           scopeImps <- getToBind {e=e'} env'
           -- note the names as now being bound implicits, so we don't bind again
           setBound (map fst scopeImps)
           st' <- strengthenedEState {e=e'} top loc
           put EST st'
           -- Bind implicits which were first used in
           -- the argument type 'tyv'
           -- This is only in 'PI' implicit mode - it's an error to
           -- have implicits at this level in 'PATT' implicit mode
           case (top, impmode) of
                (True, PI _) =>
                   do log 5 $ "Binding arg implicits " ++ show argImps
                      gam <- get Ctxt
                      let (scopev', scopet')
                          = bindImplicits impmode gam env'
                                          scopeImps scopev scopet
                      let (binder, bindert)
                          = bindImplicits impmode gam env
                                          argImps
                                          (Bind n (Pi rigf info tyv) scopev')
                                          TType
                      log 5 $ "Result " ++ show binder ++ " : " ++ show bindert
                      traverse implicitBind (map fst scopeImps)
                      traverse implicitBind (map fst argImps)
                      checkExp rigc process loc elabinfo env nest binder bindert expected
                _ => checkExp rigc process loc elabinfo env nest (Bind n (Pi rigf info tyv) scopev)
                                      TType expected

  checkLam : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             RigCount -> Elaborator annot -> ElabInfo annot ->
             annot -> Env Term vars -> NestedNames vars -> RigCount -> PiInfo -> Name ->
             (ty : RawImp annot) -> (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkLam rigc process elabinfo loc env nest rigl plicity n ty scope (Just (Bind bn (Pi c Explicit pty) psc))
      = do (tyv, tyt) <- check rigc process elabinfo env nest ty (Just TType)
           e' <- weakenedEState
           let rigb = rigMult rigc (min rigl c)
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check rigc process {e=e'} elabinfo (Pi rigb plicity pty :: env) 
                                     (weaken nest') scope 
                                     (Just (renameTop n psc))
           st' <- strengthenedEState (topLevel elabinfo) loc
           put EST st'
           checkExp rigc process loc elabinfo env nest (Bind n (Lam rigb plicity tyv) scopev)
                        (Bind n (Pi rigb plicity tyv) scopet)
                        (Just (Bind bn (Pi rigb plicity pty) psc))
  checkLam rigc process elabinfo loc env nest rigl plicity n ty scope expected
      = do (tyv, tyt) <- check rigc process elabinfo env nest ty (Just TType)
           let rigb = rigMult rigl rigc
           let env' : Env Term (n :: _) = Pi rigb Explicit tyv :: env
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} rigc process elabinfo env' (weaken nest') scope Nothing
           st' <- strengthenedEState (topLevel elabinfo) loc
           put EST st'
           checkExp rigc process loc elabinfo env nest (Bind n (Lam rigb plicity tyv) scopev)
                        (Bind n (Pi rigb plicity tyv) scopet)
                        expected
  
  checkLet : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             RigCount -> Elaborator annot ->
             ElabInfo annot -> annot -> Env Term vars -> NestedNames vars ->
             RigCount -> Name -> 
             (ty : RawImp annot) -> 
             (val : RawImp annot) -> 
             (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkLet rigc process elabinfo loc env nest rigl n ty val scope expected
      = do (tyv, tyt) <- check rigc process elabinfo env nest ty (Just TType)
           (valv, valt) <- check rigc process elabinfo env nest val (Just tyv)
           let rigb = rigMult rigl rigc
           let env' : Env Term (n :: _) = Let rigb valv tyv :: env
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} rigc process elabinfo env' 
                                     (weaken nest') scope (map weaken expected)
           st' <- strengthenedEState (topLevel elabinfo) loc
           put EST st'
           checkExp rigc process loc elabinfo env nest
                            (Bind n (Let rigb valv tyv) scopev)
                            (Bind n (Let rigb valv tyv) scopet)
                            expected

  makeImplicit 
          : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
            RigCount -> Elaborator annot -> annot -> Env Term vars -> NestedNames vars ->
            ElabInfo annot -> Name -> (ty : NF vars) ->
            Core annot (Term vars) 
  makeImplicit rigc process loc env nest elabinfo bn ty
      = case lookup bn (implicitsGiven elabinfo) of
             Just rawtm => 
               do gam <- get Ctxt
                  usedImp bn
                  (imptm, impty) <- checkImp rigc process elabinfo env nest rawtm (Just (quote (noGam gam) env ty))
                  pure imptm
             Nothing =>
              -- In an expression, add a hole
              -- In a pattern or type, treat as a variable to bind
               case elabMode elabinfo of
                  InExpr => 
                     do gam <- get Ctxt
                        hn <- genName (nameRoot bn)
                        addNamedHole loc hn False env (quote (noGam gam) env ty)
                        pure (mkConstantApp hn env)
                  _ =>
                     do gam <- get Ctxt
                        hn <- genName (nameRoot bn)
                        -- Add as a pattern variable, but let it unify with other
                        -- things, hence 'False' as an argument to addBoundName
                        let expected = quote (noGam gam) env ty
                        tm <- addBoundName loc hn False env expected
                        log 5 $ "Added Bound implicit " ++ show (hn, (tm, expected))
                        est <- get EST
                        put EST (record { boundNames $= ((hn, (tm, expected)) :: ),
                                          toBind $= ((hn, (tm, expected)) :: ) } est)
                        pure tm
  makeAutoImplicit 
          : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
            RigCount -> Elaborator annot -> annot -> Env Term vars -> NestedNames vars ->
            ElabInfo annot -> Name -> (ty : NF vars) ->
            Core annot (Term vars) 
  makeAutoImplicit rigc process loc env nest elabinfo bn ty
      = case lookup bn (implicitsGiven elabinfo) of
             Just rawtm =>
               do gam <- get Ctxt
                  usedImp bn
                  (imptm, impty) <- checkImp rigc process elabinfo env nest rawtm (Just (quote (noGam gam) env ty))
                  pure imptm
             Nothing => 
               -- on the LHS, just treat it as an implicit pattern variable.
               -- on the RHS, add a searchable hole
               case elabMode elabinfo of
                    InLHS => 
                       do gam <- get Ctxt
                          hn <- genName (nameRoot bn)
                          addNamedHole loc hn False env (quote (noGam gam) env ty)
                          pure (mkConstantApp hn env)
                    _ => 
                       do gam <- get Ctxt
                          n <- addSearchable loc env (quote (noGam gam) env ty) 500
                          log 0 $ "Auto implicit search: " ++ show n ++
                                  " for " ++ show (quote (noGam gam) env ty)
                          solveConstraints InTerm False
                          pure (mkConstantApp n env)

  -- Get the implicit arguments that need to be inserted at this point
  -- in a function application. Do this by reading off implicit Pis
  -- in the expected type ('ty') and adding new holes for each.
  -- Return the (normalised) remainder of the type, and the list of
  -- implicits added
  getImps : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
            RigCount -> Elaborator annot -> annot -> Env Term vars -> NestedNames vars ->
            ElabInfo annot ->
            (ty : NF vars) -> List (Term vars) ->
            Core annot (NF vars, List (Term vars)) 
  getImps rigc process loc env nest elabinfo (NBind bn (Pi c Implicit ty) sc) imps
      = do tm <- makeImplicit rigc process loc env nest elabinfo bn ty
           getImps rigc process loc env nest elabinfo 
                   (sc (toClosure False env tm)) (tm :: imps)
  getImps rigc process loc env nest elabinfo (NBind bn (Pi c AutoImplicit ty) sc) imps
      = do tm <- makeAutoImplicit rigc process loc env nest elabinfo bn ty
           getImps rigc process loc env nest elabinfo 
                   (sc (toClosure False env tm)) (tm :: imps)
  getImps rigc process loc env nest elabinfo ty imps = pure (ty, reverse imps)

  --- When converting, add implicits until we've applied enough for the
  --- expected type
  convertImps : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
                {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
                RigCount -> Elaborator annot -> annot -> Env Term vars ->
                NestedNames vars -> ElabInfo annot ->
                (got : NF vars) -> (exp : NF vars) -> List (Term vars) ->
                Core annot (NF vars, List (Term vars))
  convertImps rigc process loc env nest elabinfo (NBind bn (Pi c Implicit ty) sc) (NBind bn' (Pi c' Implicit ty') sc') imps
      = pure (NBind bn (Pi c Implicit ty) sc, reverse imps)
  convertImps rigc process loc env nest elabinfo (NBind bn (Pi c Implicit ty) sc) exp imps
      = do tm <- makeImplicit rigc process loc env nest elabinfo bn ty
           convertImps rigc process loc env nest elabinfo 
                       (sc (toClosure False env tm)) exp (tm :: imps)
  convertImps rigc process loc env nest elabinfo (NBind bn (Pi c AutoImplicit ty) sc) exp imps
      = do tm <- makeAutoImplicit rigc process loc env nest elabinfo bn ty
           convertImps rigc process loc env nest elabinfo 
                       (sc (toClosure False env tm)) exp (tm :: imps)
  convertImps rigc process loc env nest elabinfo got exp imps = pure (got, reverse imps)

  checkExp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
             RigCount -> Elaborator annot -> annot -> ElabInfo annot -> Env Term vars ->
             NestedNames vars ->
             (term : Term vars) -> (got : Term vars) -> 
             (exp : Maybe (Term vars)) ->
             Core annot (Term vars, Term vars) 
  checkExp rigc process loc elabinfo env nest tm got Nothing
      = do gam <- getCtxt
           pure (eraseForced gam tm, got)
  checkExp rigc process loc elabinfo env nest tm got (Just exp) 
      = do gam <- get Ctxt
           let expnf = nf gam env exp
           (got', imps) <- convertImps rigc process loc env nest elabinfo (nf gam env got) expnf []
           constr <- convert loc (elabMode elabinfo) env got' expnf
           case constr of
                [] => pure (eraseForced (gamma gam) (apply tm imps), quote (noGam gam) env got')
                cs => do gam <- getCtxt
                         c <- addConstant loc env (apply tm imps) exp cs
                         dumpConstraints 4 False
                         pure (mkConstantApp c env, got)

