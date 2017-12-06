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

-- Get the implicit arguments that need to be inserted at this point
-- in a function application. Do this by reading off implicit Pis
-- in the expected type ('ty') and adding new holes for each.
-- Return the (normalised) remainder of the type, and the list of
-- implicits added
getImps : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
          {auto e : Ref EST (EState vars)} ->
          annot -> Env Term vars -> ElabInfo vars ->
          (ty : NF vars) -> List (Term vars) ->
          Core annot (NF vars, List (Term vars)) 
getImps loc env elabinfo (NBind bn (Pi Implicit ty) sc) imps
    = case lookup bn (implicitsGiven elabinfo) of
           Just (imptm, impty) =>
             do usedImp bn
                (tmc, tyc) <- checkExp loc elabinfo env imptm impty 
                                       (Just (quote empty env ty))
                getImps loc env elabinfo (sc (toClosure True env tmc)) (tmc :: imps)
           Nothing =>
            -- In an expression, add a hole
            -- In a pattern or type, treat as a variable to bind
             case elabMode elabinfo of
                InExpr => 
                   do hn <- genName (nameRoot bn)
                      addNamedHole loc hn False env (quote empty env ty)
                      let arg = mkConstantApp hn env
                      getImps loc env elabinfo (sc (toClosure True env arg)) (arg :: imps)
                _ =>
                   do hn <- genName (nameRoot bn)
                      -- Add as a pattern variable, but let it unify with other
                      -- things, hence 'False' as an argument to addBoundName
                      let expected = quote empty env ty
                      tm <- addBoundName loc hn False env expected
                      log 5 $ "Added Bound implicit " ++ show (hn, (tm, expected))
                      est <- get EST
                      put EST (record { boundNames $= ((hn, (tm, expected)) :: ),
                                        toBind $= ((hn, (tm, expected)) :: ) } est)
                      getImps loc env elabinfo (sc (toClosure True env tm)) (tm :: imps)

getImps loc env elabinfo (NBind bn (Pi AutoImplicit ty) sc) imps
    = case lookup bn (implicitsGiven elabinfo) of
           Just (imptm, impty) =>
             do usedImp bn
                (tmc, tyc) <- checkExp loc elabinfo env imptm impty 
                                       (Just (quote empty env ty))
                getImps loc env elabinfo (sc (toClosure True env tmc)) (tmc :: imps)
           Nothing => 
             -- on the LHS, just treat it as an implicit pattern variable.
             -- on the RHS, add a searchable hole
             case elabMode elabinfo of
                  InLHS => 
                     do hn <- genName (nameRoot bn)
                        addNamedHole loc hn False env (quote empty env ty)
                        let arg = mkConstantApp hn env
                        getImps loc env elabinfo (sc (toClosure True env arg)) (arg :: imps)
                  _ => 
                     do n <- addSearchable loc env (quote empty env ty) 500
                        log 0 $ "Auto implicit search: " ++ show n ++
                                " for " ++ show (quote empty env ty)
                        solveConstraints InTerm
                        let arg = mkConstantApp n env
                        getImps loc env elabinfo (sc (toClosure True env arg)) (arg :: imps)
getImps loc env elabinfo ty imps = pure (ty, reverse imps)


-- Check a name. At this point, we've already established that it's not
-- one of the local definitions, so it either must be a local variable or
-- a globally defined name
checkName : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
            ElabInfo vars -> annot -> Env Term vars -> Name -> Maybe (Term vars) ->
            Core annot (Term vars, Term vars)
checkName {vars} elabinfo loc env x expected 
    = do gam <- getCtxt
         case defined x env of
           Just lv => 
               do let varty = binderType (getBinder lv env) 
                  (ty, imps) <- getImps loc env elabinfo (nf gam env varty) []
                  checkExp loc elabinfo env (apply (Local lv) imps)
                          (quote empty env ty) expected
           Nothing =>
                  case lookupDefTyName x gam of
                       [] => throw $ UndefinedName loc x
                       [(fullname, def, ty)] => 
                            resolveRef fullname def gam (embed ty)
                       ns => exactlyOne loc (map (\ (n, def, ty) =>
                                     resolveRef n def gam (embed ty)) ns)
  where
    resolveRef : Name -> Def -> Gamma -> Term vars -> 
                 Core annot (Term vars, Term vars)
    resolveRef n def gam varty
        = do let nt : NameType 
                      = case def of
                           PMDef _ _ _ => Func
                           DCon tag arity => DataCon tag arity
                           TCon tag arity _ => TyCon tag arity
                           _ => Func
             (ty, imps) <- getImps loc env elabinfo (nf gam env varty) []
             checkExp loc elabinfo env (apply (Ref nt n) imps) 
                          (quote empty env ty) expected
  
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
    bindLam tm (Bind n (Pi Implicit ty) sc)
        = let loc = getAnnot tm in
              ILam loc Implicit n (Implicit loc) (bindLam tm sc)
    bindLam tm sc = tm

expandAmbigName : Gamma -> Env Term vars -> NestedNames vars ->
                  RawImp annot -> 
                  List (annot, RawImp annot) -> RawImp annot -> RawImp annot
expandAmbigName gam env nest orig args (IVar loc x)
   = case lookup x (names nest) of
          Just _ => orig
          Nothing => 
            case defined x env of
                 Just _ => orig
                 Nothing => case lookupCtxtName x gam of
                                 [] => orig
                                 ns => IAlternative loc True
                                         (map (\n => buildAlt (IVar loc n) args) 
                                              (map fst ns))
  where
    buildAlt : RawImp annot -> List (annot, RawImp annot) -> RawImp annot
    buildAlt f [] = f
    buildAlt f ((loc, a) :: as) = buildAlt (IApp loc f a) as
expandAmbigName gam env nest orig args (IApp loc f a)
   = expandAmbigName gam env nest orig ((loc, a) :: args) f
expandAmbigName gam env nest orig args _ = orig

mutual
  export
  check : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
          {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
          Elaborator annot -> -- the elaborator for top level declarations
                              -- used for nested definitions
          ElabInfo vars -> -- elaboration parameters
          Env Term vars -> -- bound names (lambda, pi, let)
          NestedNames vars -> -- locally defined names (arising from nested top level
                              -- declarations)
          (term : RawImp annot) -> -- Term to elaborate
          (expected : Maybe (Term vars)) -> -- Expected type, if available
          Core annot (Term vars, Term vars) 
  check process elabinfo env nest tm_in exp 
      = do gam <- getCtxt
           let tm = expandAmbigName gam env nest tm_in [] tm_in
           case elabMode elabinfo of
               -- don't expand implicit lambda on LHS
               InLHS => checkImp process elabinfo env nest tm exp
               _ => let tm' = insertImpLam env tm exp in
                        checkImp process elabinfo env nest tm' exp

  checkImp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             ElabInfo vars ->
             Env Term vars -> NestedNames vars ->
             (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
             Core annot (Term vars, Term vars) 
  checkImp process elabinfo env nest (IVar loc x) expected 
      = case lookup x (names nest) of
             Just (n', tm) =>
                  do gam <- getCtxt
                     case lookupTyExact n' gam of
                          Nothing => throw (UndefinedName loc n')
                          Just ty => 
                             let tyenv = useVars (getArgs tm) (embed ty) in
                                do log 5 $ "Type of " ++ show n' ++ " : " ++ show tyenv
                                   checkExp loc elabinfo env tm tyenv expected
             _ => checkName elabinfo loc env x expected
    where
      useVars : List (Term vars) -> Term vars -> Term vars
      useVars [] sc = sc
      useVars (a :: as) (Bind n (Pi _ ty) sc) 
           = Bind n (Let a ty) (useVars (map weaken as) sc)
      useVars _ sc = sc -- Can't happen?
  checkImp process elabinfo env nest (IPi loc plicity Nothing ty retTy) expected 
      = do n <- genName "pi"
           checkPi process elabinfo loc env nest plicity n ty retTy expected
  checkImp process elabinfo env nest (IPi loc plicity (Just n) ty retTy) expected 
      = checkPi process elabinfo loc env nest plicity n ty retTy expected
  checkImp process elabinfo env nest (ILam loc plicity n ty scope) expected
      = checkLam process elabinfo loc env nest plicity n ty scope expected
  checkImp process elabinfo env nest (ILet loc n nTy nVal scope) expected 
      = checkLet process elabinfo loc env nest n nTy nVal scope expected
  checkImp {vars} {c} {u} {i} process elabinfo env nest (ILocal loc nested scope) expected 
      = do let defNames = definedInBlock nested
           est <- get EST
           let f = defining est
           let nest' = record { names $= ((map (applyEnv f) defNames) ++) } nest
           traverse (process c u i env nest') (map (updateName nest') nested)
           checkImp process elabinfo env nest' scope expected
    where
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
      updateTyName nest (MkImpTy loc n ty) = MkImpTy loc (newName nest n) ty

      updateDataName : NestedNames vars -> ImpData annot -> ImpData annot
      updateDataName nest (MkImpData loc n tycons dcons)
          = MkImpData loc (newName nest n) tycons (map (updateTyName nest) dcons)

      updateName : NestedNames vars -> ImpDecl annot -> ImpDecl annot
      updateName nest (IClaim loc ty) = IClaim loc (updateTyName nest ty)
      updateName nest (IDef loc n cs) = IDef loc (newName nest n) cs
      updateName nest (IData loc d) = IData loc (updateDataName nest d)
      updateName nest i = i

  checkImp process elabinfo env nest (IApp loc fn arg) expected 
      = do -- Collect the implicits from the top level application first
           let (fn', args) = collectGivenImps fn
           elabinfo' <- checkGivenImps process elabinfo env nest args
           log 10 $ "Implicits: " ++ show (implicitsGiven elabinfo')
           (restm, resty) <- checkApp process elabinfo' loc env nest fn' arg expected
           -- Add any remaining implicits greedily
           gam <- getCtxt
           (ty, imps) <- getImps loc env elabinfo' (nf gam env resty) []
           -- Check all of the implicits we collected have been used
           est <- get EST
           log 10 $ "Used: " ++ show (implicitsUsed est, map fst args)
           checkUsedImplicits loc (implicitsUsed est) (map fst args) restm
           case imps of
                [] => pure (restm, resty)
                _ => checkExp loc elabinfo env (apply restm imps) (quote empty env ty) expected
  checkImp process elabinfo env nest (IImplicitApp loc fn nm arg) expected 
      = do let (fn', args) = collectGivenImps fn
           elabinfo' <- checkGivenImps process elabinfo env nest ((nm, arg) :: args)
           log 10 $ "IImplicits: " ++ show (implicitsGiven elabinfo')
           (restm, resty) <- checkImp process elabinfo' env nest fn' expected
           -- Add any remaining implicits greedily
           gam <- getCtxt
           (ty, imps) <- getImps loc env elabinfo' (nf gam env resty) []
           -- Check all of the implicits we collected have been used
           est <- get EST
           log 10 $ "IUsed: " ++ show (implicitsUsed est, nm :: map fst args)
           checkUsedImplicits loc (implicitsUsed est) (nm :: map fst args) restm
           case imps of
                [] => pure (restm, resty)
                _ => checkExp loc elabinfo env (apply restm imps) (quote empty env ty) expected
  checkImp process elabinfo env nest (ISearch loc depth) Nothing
      = throw (InternalError "Trying to search for a term with an unknown type")
  checkImp process elabinfo env nest (ISearch loc depth) (Just expected)
      = do n <- addSearchable loc env expected depth
           let umode = case elabMode elabinfo of
                            InLHS => InLHS
                            _ => InTerm
           -- try again to solve the holes, including the search we've just added.
           solveConstraints umode
           pure (mkConstantApp n env, expected)
  -- TODO: On failure to disambiguate, postpone? Would need another unification
  -- tactic, like 'search' is...
  checkImp process elabinfo env nest (IAlternative loc uniq alts) expected
      = let tryall = if uniq then exactlyOne else anyOne in
            tryall loc (map (\t => 
                    checkImp process elabinfo env nest t expected) alts)
  checkImp process elabinfo env nest (IPrimVal loc x) expected 
      = do (x', ty) <- infer loc env (RPrimVal x)
           checkExp loc elabinfo env x' ty expected
  checkImp process elabinfo env nest (IType loc) exp
      = checkExp loc elabinfo env TType TType exp
  checkImp process elabinfo env nest (IBindVar loc str) exp with (elabMode elabinfo)
    checkImp process elabinfo env nest (IBindVar loc str) exp | InExpr
      = throw (BadImplicit loc str)
    checkImp process elabinfo env nest (IBindVar loc str) Nothing | elabmode
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
    checkImp process elabinfo env nest (IBindVar loc str) (Just expected) | elabmode
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
                       checkExp loc elabinfo env tm ty (Just expected)
  checkImp process elabinfo env nest (IMustUnify loc tm) (Just expected) with (elabMode elabinfo)
    checkImp process elabinfo env nest (IMustUnify loc tm) (Just expected) | InLHS
      = do (wantedTm, wantedTy) <- checkImp process elabinfo env nest tm (Just expected)
           n <- addHole loc env expected
           gam <- getCtxt
           let tm = mkConstantApp n env
           addDot loc env wantedTm tm
           checkExp loc elabinfo env tm wantedTy (Just expected)
    checkImp process elabinfo env nest (IMustUnify loc tm) (Just expected) | elabmode
        = throw (GenericMsg loc "Dot pattern not valid here")
  checkImp process elabinfo env nest (IMustUnify loc tm) expected
      = throw (GenericMsg loc "Dot pattern not valid here")
  checkImp process elabinfo env nest (IAs loc var tm) expected with (elabMode elabinfo)
    checkImp process elabinfo env nest (IAs loc var tm) (Just expected) | InLHS
      = checkAs process elabinfo loc env nest var tm expected
    checkImp process elabinfo env nest (IAs loc var tm) expected | elabmode
        = throw (GenericMsg loc "@-pattern not valid here")
  checkImp process elabinfo env nest (IHole loc n_in) Nothing
      = do t <- addHole loc env TType
           let hty = mkConstantApp t env
           n <- inCurrentNS (UN n_in)
           addNamedHole loc n False env hty
           pure (mkConstantApp n env, hty)
  checkImp process elabinfo env nest (IHole loc n_in) (Just expected) 
      = do n <- inCurrentNS (UN n_in)
           addNamedHole loc n False env expected
           pure (mkConstantApp n env, expected)
  checkImp process elabinfo env nest (Implicit loc) Nothing
      = do t <- addHole loc env TType
           let hty = mkConstantApp t env
           n <- addHole loc env hty
           pure (mkConstantApp n env, hty)
  checkImp process elabinfo env nest (Implicit loc) (Just expected) 
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

  checkGivenImp
          : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot ->
            ElabInfo vars -> Env Term vars -> NestedNames vars -> 
            (Name, RawImp annot) ->
            Core annot (Name, Term vars, Term vars) 
  checkGivenImp process elabinfo env nest (n, tm) 
      = do (argTm, argTy) <- checkImp process elabinfo env nest tm Nothing
           -- TODO: error if 'n' already in (implicitsGiven elabinfo)
           pure (n, argTm, argTy)

  checkGivenImps
          : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot ->
            ElabInfo vars -> Env Term vars -> NestedNames vars -> 
            List (Name, RawImp annot) ->
            Core annot (ElabInfo vars)
  checkGivenImps process elabinfo env nest args
      = do given <- traverse (checkGivenImp process elabinfo env nest) args
           pure (record { implicitsGiven $= (given ++) } elabinfo)

  checkAs : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot ->
            ElabInfo vars -> annot -> Env Term vars -> NestedNames vars -> 
            String -> (arg : RawImp annot) ->
            Term vars ->
            Core annot (Term vars, Term vars) 
  checkAs process elabinfo loc env nest var tm expected
      = do let n = PV var
           est <- get EST
           (patTm, patTy) <- checkImp process elabinfo env nest tm (Just expected)
           addBoundName loc n False env expected
           case lookup n (boundNames est) of
                Just (tm, ty) =>
                    throw (GenericMsg loc ("Name " ++ var ++ " already bound"))
                Nothing =>
                    do tm <- addBoundName loc n False env expected
                       log 5 $ "Added @ pattern name " ++ show (n, (tm, expected))
                       put EST
                           (record { boundNames $= ((n, (tm, expected)) ::),
                                     toBind $= ((n, (tm, expected)) ::) } est)
                       gam <- getCtxt
                       convert loc InLHS env (nf gam env patTm) (nf gam env tm)
                       pure (patTm, expected)

  checkApp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             ElabInfo vars -> annot -> Env Term vars -> NestedNames vars -> 
             (fn : RawImp annot) -> (arg : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkApp process elabinfo loc env nest fn arg expected
      = do (fntm, fnty) <- check process elabinfo env nest fn Nothing
           gam <- getCtxt
           case nf gam env fnty of
                NBind _ (Pi _ ty) scdone =>
                  do impsUsed <- saveImps
                     (argtm, argty) <- check process (record { implicitsGiven = [] } elabinfo)
                                             env nest arg (Just (quote empty env ty))
                     restoreImps impsUsed
                     let sc' = scdone (toClosure False env argtm)
                     gam <- getCtxt
                     checkExp loc elabinfo env (App fntm argtm)
                                  (quote gam env sc') expected
                _ => 
                  do bn <- genName "aTy"
                     -- invent names for the argument and return types
                     log 5 $ "Inventing arg type for " ++ show (fn, fnty)
                     (expty, scty) <- inventFnType loc env bn
                     -- Check the argument type against the invented arg type
                     impsUsed <- saveImps
                     (argtm, argty) <- check process (record { implicitsGiven = [] } elabinfo)
                                             env nest arg (Just expty)
                     restoreImps impsUsed
                     -- Check the type of 'fn' is an actual function type
                     gam <- getCtxt
                     (fnchk, _) <-
                         checkExp loc elabinfo env fntm 
                                  (Bind bn (Pi Explicit expty) scty) 
                                  (Just (quote gam env fnty))
                     checkExp loc elabinfo env (App fnchk argtm)
                                  (Bind bn (Let argtm argty) scty) expected


  checkPi : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot -> ElabInfo vars ->
            annot -> Env Term vars -> NestedNames vars -> PiInfo -> Name -> 
            (argty : RawImp annot) -> (retty : RawImp annot) ->
            Maybe (Term vars) ->
            Core annot (Term vars, Term vars) 
  checkPi process elabinfo loc env nest info n argty retty expected
      = do let top = topLevel elabinfo
           let impmode = implicitMode elabinfo
           let elabmode = elabMode elabinfo
           (tyv, tyt) <- check process (record { topLevel = False } elabinfo) 
                               env nest argty (Just TType)
           let env' : Env Term (n :: _) = Pi info tyv :: env
           est <- get EST
           
           tobind <- getToBind env
           let argImps = if top then tobind else []
           -- note the names as now being bound implicits, so we don't bind again
           setBound (map fst argImps)
           when top $ clearToBind 
           e' <- weakenedEState 
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} process (weaken elabinfo) env' (weaken nest') retty (Just TType)
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
                      gam <- getCtxt
                      let (scopev', scopet')
                          = bindImplicits impmode gam env'
                                          scopeImps scopev scopet
                      let (binder, bindert)
                          = bindImplicits impmode gam env
                                          argImps
                                          (Bind n (Pi info tyv) scopev')
                                          TType
                      log 5 $ "Result " ++ show binder ++ " : " ++ show bindert
                      traverse implicitBind (map fst scopeImps)
                      traverse implicitBind (map fst argImps)
                      checkExp loc elabinfo env binder bindert expected
                _ => checkExp loc elabinfo env (Bind n (Pi info tyv) scopev)
                                      TType expected

  checkLam : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot -> ElabInfo vars ->
             annot -> Env Term vars -> NestedNames vars -> PiInfo -> Name ->
             (ty : RawImp annot) -> (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkLam process elabinfo loc env nest plicity n ty scope (Just (Bind bn (Pi Explicit pty) psc))
      = do (tyv, tyt) <- check process elabinfo env nest ty (Just TType)
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check process {e=e'} (weaken elabinfo) (Pi plicity pty :: env) 
                                     (weaken nest') scope 
                                     (Just (renameTop n psc))
           st' <- strengthenedEState (topLevel elabinfo) loc
           put EST st'
           checkExp loc elabinfo env (Bind n (Lam plicity tyv) scopev)
                        (Bind n (Pi plicity tyv) scopet)
                        (Just (Bind bn (Pi plicity pty) psc))
  checkLam process elabinfo loc env nest plicity n ty scope expected
      = do (tyv, tyt) <- check process elabinfo env nest ty (Just TType)
           let env' : Env Term (n :: _) = Pi Explicit tyv :: env
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} process (weaken elabinfo) env' (weaken nest') scope Nothing
           st' <- strengthenedEState (topLevel elabinfo) loc
           put EST st'
           checkExp loc elabinfo env (Bind n (Lam plicity tyv) scopev)
                        (Bind n (Pi plicity tyv) scopet)
                        expected
  
  checkLet : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             ElabInfo vars -> annot -> Env Term vars -> NestedNames vars ->
             Name -> 
             (ty : RawImp annot) -> 
             (val : RawImp annot) -> 
             (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkLet process elabinfo loc env nest n ty val scope expected
      = do (tyv, tyt) <- check process elabinfo env nest ty (Just TType)
           (valv, valt) <- check process elabinfo env nest val (Just tyv)
           let env' : Env Term (n :: _) = Let valv tyv :: env
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} process (weaken elabinfo) env' 
                                     (weaken nest') scope (map weaken expected)
           st' <- strengthenedEState (topLevel elabinfo) loc
           put EST st'
           checkExp loc elabinfo env (Bind n (Let valv tyv) scopev)
                                     (Bind n (Let valv tyv) scopet)
                                     expected
