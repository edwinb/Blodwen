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
    buildAlt f ((loc', a) :: as) = buildAlt (IApp loc' f a) as
expandAmbigName gam env nest orig args (IApp loc f a)
   = expandAmbigName gam env nest orig ((loc, a) :: args) f
expandAmbigName gam env nest orig args _ = orig

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

mutual
  export
  check : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
          {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
          Elaborator annot -> -- the elaborator for top level declarations
                              -- used for nested definitions
          ElabInfo annot -> -- elaboration parameters
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
             ElabInfo annot ->
             Env Term vars -> NestedNames vars ->
             (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
             Core annot (Term vars, Term vars) 
  checkImp process elabinfo env nest (IVar loc x) expected 
      = case lookup x (names nest) of
             Just (n', tm) =>
                  do gam <- getCtxt
                     case lookupTyExact n' gam of
                          Nothing => throw (UndefinedName loc n')
                          Just varty => 
                             do let tyenv = useVars (getArgs tm) (embed varty)
                                (ty_nf, imps) <- getImps process loc env nest elabinfo (nf gam env tyenv) []
                                let ty = quote empty env ty_nf
                                log 5 $ "Type of " ++ show n' ++ " : " ++ show ty
                                log 5 $ "Term: " ++ show (apply tm imps)
                                checkExp process loc elabinfo env nest 
                                         (apply tm imps) ty expected
             _ => checkName process elabinfo loc env nest x expected
    where
      useVars : List (Term vars) -> Term vars -> Term vars
      useVars [] sc = sc
      useVars (a :: as) (Bind n (Pi _ ty) sc) 
           = Bind n (Let a ty) (useVars (map weaken as) sc)
      useVars _ sc = sc -- Can't happen?
  checkImp process elabinfo env nest (IPi loc plicity Nothing ty retTy) expected 
      = do n <- genName "pi"
           checkPi process elabinfo loc env nest plicity (dropNS n) ty retTy expected
  checkImp process elabinfo env nest (IPi loc plicity (Just n) ty retTy) expected 
      = checkPi process elabinfo loc env nest plicity n ty retTy expected
  checkImp process elabinfo env nest (ILam loc plicity n ty scope) expected
      = checkLam process elabinfo loc env nest plicity n ty scope expected
  checkImp process elabinfo env nest (ILet loc n nTy nVal scope) expected 
      = checkLet process elabinfo loc env nest n nTy nVal scope expected
  checkImp {vars} {c} {u} {i} process elabinfo env nest (ICase loc scr alts) expected 
      = do (scrtm, scrty) <- check process elabinfo env nest scr Nothing
           log 0 $ "Expected: " ++ show expected
           log 0 $ "Scrutinee: " ++ show scrtm ++ " : " ++ show scrty
           log 0 $ "Env: " ++ show env
           log 0 $ "Alts: " ++ show alts
           throw (InternalError "Case not yet implemented")
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
      updateTyName nest (MkImpTy loc' n ty) = MkImpTy loc' (newName nest n) ty

      updateDataName : NestedNames vars -> ImpData annot -> ImpData annot
      updateDataName nest (MkImpData loc' n tycons dcons)
          = MkImpData loc' (newName nest n) tycons (map (updateTyName nest) dcons)

      updateName : NestedNames vars -> ImpDecl annot -> ImpDecl annot
      updateName nest (IClaim loc' ty) = IClaim loc' (updateTyName nest ty)
      updateName nest (IDef loc' n cs) = IDef loc' (newName nest n) cs
      updateName nest (IData loc' d) = IData loc' (updateDataName nest d)
      updateName nest i = i

  checkImp process elabinfo env nest (IApp loc fn arg) expected 
      = do -- Collect the implicits from the top level application first
           let (fn', args) = collectGivenImps fn
           let elabinfo' = addGivenImps elabinfo args
           log 10 $ "Implicits: " ++ show (implicitsGiven elabinfo')
           (restm, resty) <- checkApp process elabinfo' loc env nest fn' arg expected
           -- Add any remaining implicits greedily
           gam <- getCtxt
           (ty, imps) <- getImps process loc env nest elabinfo' (nf gam env resty) []
           log 10 $ "Checked app " ++ show (restm, quote empty env ty, imps)
           -- Check all of the implicits we collected have been used
           est <- get EST
           log 10 $ "Used: " ++ show (implicitsUsed est, map fst args)
           checkUsedImplicits loc (implicitsUsed est) (map fst args) (apply restm imps)
           case imps of
                [] => pure (restm, resty)
                _ => checkExp process loc elabinfo env nest (apply restm imps) 
                              (quote empty env ty) expected
  checkImp process elabinfo env nest (IImplicitApp loc fn nm arg) expected 
      = do let (fn', args) = collectGivenImps fn
           let elabinfo' = addGivenImps elabinfo ((nm, arg) :: args)
           log 10 $ "IImplicits: " ++ show (implicitsGiven elabinfo')
           (restm, resty) <- check process elabinfo' env nest fn' expected
           -- Add any remaining implicits greedily
           gam <- getCtxt
           (ty, imps) <- getImps process loc env nest elabinfo' (nf gam env resty) []
           log 10 $ "Checked app " ++ show (restm, quote empty env ty, imps)
           -- Check all of the implicits we collected have been used
           est <- get EST
           log 10 $ "IUsed: " ++ show (implicitsUsed est, nm :: map fst args)
           checkUsedImplicits loc (implicitsUsed est) (nm :: map fst args) (apply restm imps)
           case imps of
                [] => pure (restm, resty)
                _ => checkExp process loc elabinfo env nest (apply restm imps) 
                              (quote empty env ty) expected
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
           checkExp process loc elabinfo env nest x' ty expected
  checkImp process elabinfo env nest (IType loc) exp
      = checkExp process loc elabinfo env nest TType TType exp
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
                       if repeatBindOK (dotted elabinfo) (elabMode elabinfo)
                          then checkExp process loc elabinfo env nest tm ty (Just expected)
                          else throw (NonLinearPattern loc n)
      where
        repeatBindOK : Bool -> ElabMode -> Bool
        repeatBindOK False InLHS = False
        repeatBindOK _ _ = True
  checkImp process elabinfo env nest (IMustUnify loc tm) (Just expected) with (elabMode elabinfo)
    checkImp process elabinfo env nest (IMustUnify loc tm) (Just expected) | InLHS
      = do (wantedTm, wantedTy) <- checkImp process 
                                            (record { dotted = True } elabinfo)
                                            env nest tm (Just expected)
           n <- addHole loc env expected
           gam <- getCtxt
           let tm = mkConstantApp n env
           addDot loc env wantedTm tm
           checkExp process loc elabinfo env nest tm wantedTy (Just expected)
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

  addGivenImps : ElabInfo annot -> List (Name, RawImp annot) -> ElabInfo annot
  addGivenImps elabinfo ns = record { implicitsGiven $= (ns ++) } elabinfo

  -- Check a name. At this point, we've already established that it's not
  -- one of the local definitions, so it either must be a local variable or
  -- a globally defined name
  checkName : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
              {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
              Elaborator annot -> ElabInfo annot -> annot -> Env Term vars -> 
              NestedNames vars -> Name -> Maybe (Term vars) ->
              Core annot (Term vars, Term vars)
  checkName {vars} process elabinfo loc env nest x expected 
      = do gam <- getCtxt
           case defined x env of
             Just lv => 
                 do let varty = binderType (getBinder lv env) 
                    (ty, imps) <- getImps process loc env nest elabinfo (nf gam env varty) []
                    checkExp process loc elabinfo env nest (apply (Local lv) imps)
                            (quote empty env ty) expected
             Nothing =>
                    case lookupDefTyName x gam of
                         [] => throw $ UndefinedName loc x
                         [(fullname, def, ty)] => 
                              resolveRef fullname def gam (embed ty)
                         ns => exactlyOne loc (map (\ (n, def, ty) =>
                                       resolveRef n def gam (embed ty)) ns)
    where
      defOK : Bool -> ElabMode -> NameType -> Bool
      defOK False InLHS (DataCon _ _) = True
      defOK False InLHS _ = False
      defOK _ _ _ = True

      resolveRef : Name -> Def -> Gamma -> Term vars -> 
                   Core annot (Term vars, Term vars)
      resolveRef n def gam varty
          = do let nt : NameType 
                        = case def of
                             PMDef _ _ _ => Func
                             DCon tag arity _ => DataCon tag arity
                             TCon tag arity _ _ => TyCon tag arity
                             _ => Func
               (ty, imps) <- getImps process loc env nest elabinfo (nf gam env varty) []
               if topLevel elabinfo ||
                    defOK (dotted elabinfo) (elabMode elabinfo) nt
                  then checkExp process loc elabinfo env nest (apply (Ref nt n) imps) 
                            (quote empty env ty) expected
                  else throw (BadPattern loc n)

  checkAs : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot ->
            ElabInfo annot -> annot -> Env Term vars -> NestedNames vars -> 
            String -> (arg : RawImp annot) ->
            Term vars ->
            Core annot (Term vars, Term vars) 
  checkAs process elabinfo loc env nest var tm expected
      = do let n = PV var
           (patTm, patTy) <- checkImp process elabinfo env nest tm (Just expected)
           addBoundName loc n False env expected
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
                       gam <- getCtxt
                       convert loc InLHS env (nf gam env patTm) (nf gam env tm)
                       pure (patTm, expected)

  checkApp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             ElabInfo annot -> annot -> Env Term vars -> NestedNames vars -> 
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
                     checkExp process loc elabinfo env nest (App fntm argtm)
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
                         checkExp process loc elabinfo env nest fntm 
                                  (Bind bn (Pi Explicit expty) scty) 
                                  (Just (quote gam env fnty))
                     checkExp process loc elabinfo env nest (App fnchk argtm)
                                  (Bind bn (Let argtm argty) scty) expected

  checkPi : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot -> ElabInfo annot ->
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
           (scopev, scopet) <- check {e=e'} process elabinfo env' (weaken nest') retty (Just TType)
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
                      checkExp process loc elabinfo env nest binder bindert expected
                _ => checkExp process loc elabinfo env nest (Bind n (Pi info tyv) scopev)
                                      TType expected

  checkLam : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot -> ElabInfo annot ->
             annot -> Env Term vars -> NestedNames vars -> PiInfo -> Name ->
             (ty : RawImp annot) -> (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkLam process elabinfo loc env nest plicity n ty scope (Just (Bind bn (Pi Explicit pty) psc))
      = do (tyv, tyt) <- check process elabinfo env nest ty (Just TType)
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check process {e=e'} elabinfo (Pi plicity pty :: env) 
                                     (weaken nest') scope 
                                     (Just (renameTop n psc))
           st' <- strengthenedEState (topLevel elabinfo) loc
           put EST st'
           checkExp process loc elabinfo env nest (Bind n (Lam plicity tyv) scopev)
                        (Bind n (Pi plicity tyv) scopet)
                        (Just (Bind bn (Pi plicity pty) psc))
  checkLam process elabinfo loc env nest plicity n ty scope expected
      = do (tyv, tyt) <- check process elabinfo env nest ty (Just TType)
           let env' : Env Term (n :: _) = Pi Explicit tyv :: env
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} process elabinfo env' (weaken nest') scope Nothing
           st' <- strengthenedEState (topLevel elabinfo) loc
           put EST st'
           checkExp process loc elabinfo env nest (Bind n (Lam plicity tyv) scopev)
                        (Bind n (Pi plicity tyv) scopet)
                        expected
  
  checkLet : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             ElabInfo annot -> annot -> Env Term vars -> NestedNames vars ->
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
           (scopev, scopet) <- check {e=e'} process elabinfo env' 
                                     (weaken nest') scope (map weaken expected)
           st' <- strengthenedEState (topLevel elabinfo) loc
           put EST st'
           checkExp process loc elabinfo env nest
                            (Bind n (Let valv tyv) scopev)
                            (Bind n (Let valv tyv) scopet)
                            expected

  makeImplicit 
          : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot -> annot -> Env Term vars -> NestedNames vars ->
            ElabInfo annot -> Name -> (ty : NF vars) ->
            Core annot (Term vars) 
  makeImplicit process loc env nest elabinfo bn ty
      = case lookup bn (implicitsGiven elabinfo) of
             Just rawtm => 
               do usedImp bn
                  (imptm, impty) <- checkImp process elabinfo env nest rawtm (Just (quote empty env ty))
                  pure imptm
             Nothing =>
              -- In an expression, add a hole
              -- In a pattern or type, treat as a variable to bind
               case elabMode elabinfo of
                  InExpr => 
                     do hn <- genName (nameRoot bn)
                        addNamedHole loc hn False env (quote empty env ty)
                        pure (mkConstantApp hn env)
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
                        pure tm
  makeAutoImplicit 
          : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot -> annot -> Env Term vars -> NestedNames vars ->
            ElabInfo annot -> Name -> (ty : NF vars) ->
            Core annot (Term vars) 
  makeAutoImplicit process loc env nest elabinfo bn ty
      = case lookup bn (implicitsGiven elabinfo) of
             Just rawtm =>
               do usedImp bn
                  (imptm, impty) <- checkImp process elabinfo env nest rawtm (Just (quote empty env ty))
                  pure imptm
             Nothing => 
               -- on the LHS, just treat it as an implicit pattern variable.
               -- on the RHS, add a searchable hole
               case elabMode elabinfo of
                    InLHS => 
                       do hn <- genName (nameRoot bn)
                          addNamedHole loc hn False env (quote empty env ty)
                          pure (mkConstantApp hn env)
                    _ => 
                       do n <- addSearchable loc env (quote empty env ty) 500
                          log 0 $ "Auto implicit search: " ++ show n ++
                                  " for " ++ show (quote empty env ty)
                          solveConstraints InTerm
                          pure (mkConstantApp n env)

  -- Get the implicit arguments that need to be inserted at this point
  -- in a function application. Do this by reading off implicit Pis
  -- in the expected type ('ty') and adding new holes for each.
  -- Return the (normalised) remainder of the type, and the list of
  -- implicits added
  getImps : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot -> annot -> Env Term vars -> NestedNames vars ->
            ElabInfo annot ->
            (ty : NF vars) -> List (Term vars) ->
            Core annot (NF vars, List (Term vars)) 
  getImps process loc env nest elabinfo (NBind bn (Pi Implicit ty) sc) imps
      = do tm <- makeImplicit process loc env nest elabinfo bn ty
           getImps process loc env nest elabinfo 
                   (sc (toClosure False env tm)) (tm :: imps)
  getImps process loc env nest elabinfo (NBind bn (Pi AutoImplicit ty) sc) imps
      = do tm <- makeAutoImplicit process loc env nest elabinfo bn ty
           getImps process loc env nest elabinfo 
                   (sc (toClosure False env tm)) (tm :: imps)
  getImps process loc env nest elabinfo ty imps = pure (ty, reverse imps)

  --- When converting, add implicits until we've applied enough for the
  --- expected type
  convertImps : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
                {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
                Elaborator annot -> annot -> Env Term vars ->
                NestedNames vars -> ElabInfo annot ->
                (got : NF vars) -> (exp : NF vars) -> List (Term vars) ->
                Core annot (NF vars, List (Term vars))
  convertImps process loc env nest elabinfo (NBind bn (Pi Implicit ty) sc) (NBind bn' (Pi Implicit ty') sc') imps
      = pure (NBind bn (Pi Implicit ty) sc, reverse imps)
  convertImps process loc env nest elabinfo (NBind bn (Pi Implicit ty) sc) exp imps
      = do tm <- makeImplicit process loc env nest elabinfo bn ty
           convertImps process loc env nest elabinfo 
                       (sc (toClosure False env tm)) exp (tm :: imps)
  convertImps process loc env nest elabinfo (NBind bn (Pi AutoImplicit ty) sc) exp imps
      = do tm <- makeAutoImplicit process loc env nest elabinfo bn ty
           convertImps process loc env nest elabinfo 
                       (sc (toClosure False env tm)) exp (tm :: imps)
  convertImps process loc env nest elabinfo got exp imps = pure (got, reverse imps)

  checkExp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot -> annot -> ElabInfo annot -> Env Term vars ->
             NestedNames vars ->
             (term : Term vars) -> (got : Term vars) -> 
             (exp : Maybe (Term vars)) ->
             Core annot (Term vars, Term vars) 
  checkExp process loc elabinfo env nest tm got Nothing
      = do gam <- getCtxt
           pure (eraseForced gam tm, got)
  checkExp process loc elabinfo env nest tm got (Just exp) 
      = do gam <- getCtxt
           let expnf = nf gam env exp
           (got', imps) <- convertImps process loc env nest elabinfo (nf gam env got) expnf []
           constr <- convert loc (elabMode elabinfo) env got' expnf
           case constr of
                [] => pure (eraseForced gam (apply tm imps), quote empty env got')
                cs => do gam <- getCtxt
                         c <- addConstant loc env (apply tm imps) exp cs
                         pure (mkConstantApp c env, got)

