module TTImp.Elab.Term

import TTImp.TTImp
import TTImp.Elab.Ambiguity
import TTImp.Elab.Case
import TTImp.Elab.Delayed
import TTImp.Elab.Record
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

-- If the expected type has an implicit pi, elaborate with leading
-- implicit lambdas if they aren't there already. 
insertImpLam : {auto c : Ref Ctxt Defs} ->
               Env Term vars ->
               (term : RawImp annot) -> (expected : ExpType (Term vars)) ->
               Core annot (RawImp annot)
insertImpLam env tm (FnType [] ty) = bindLam tm ty
  where
    bindLam : RawImp annot -> Term vars -> Core annot (RawImp annot)
    bindLam tm@(ILam _ _ Implicit _ _ _) (Bind n (Pi _ Implicit _) sc)
        = pure tm
    bindLam tm (Bind n (Pi c Implicit ty) sc)
        = do let loc = getAnnot tm
             -- Can't use the same name, there may be a clash.
             n' <- genVarName ("imp_" ++ show n)
             sc' <- bindLam tm sc
             pure $ ILam loc c Implicit (Just n') (Implicit loc) sc'
    bindLam tm sc = pure tm
insertImpLam env tm _ = pure tm

noteLHSPatVar : {auto e : Ref EST (EState vars)} ->
             ElabMode -> String -> Core annot ()
noteLHSPatVar (InLHS _) n
    = do est <- get EST
         put EST (record { lhsPatVars $= (n ::) } est)
noteLHSPatVar _ _ = pure ()

notePatVar : {auto e : Ref EST (EState vars)} ->
             Name -> Core annot ()
notePatVar n
    = do est <- get EST
         put EST (record { allPatVars $= (n ::) } est)

bindRig : RigCount -> RigCount
bindRig Rig0 = Rig0
bindRig _ = rig1
      
rewriteErr : Error annot -> Bool
rewriteErr (NotRewriteRule _ _ _) = True
rewriteErr (RewriteNoChange _ _ _ _) = True
rewriteErr (InType _ _ err) = rewriteErr err
rewriteErr (InCon _ _ err) = rewriteErr err
rewriteErr (InLHS _ _ err) = rewriteErr err
rewriteErr (InRHS _ _ err) = rewriteErr err
rewriteErr (WhenUnifying _ _ _ _ err) = rewriteErr err
rewriteErr _ = False

getName : RawImp annot -> Maybe Name
getName (IVar _ n) = Just n
getName (IApp _ f _) = getName f
getName (IImplicitApp _ f _ _) = getName f
getName _ = Nothing

mutual
  export
  check : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
          {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
          {auto m : Ref Meta (Metadata annot)} ->
          Reflect annot =>
          RigCount ->
          Elaborator annot -> -- the elaborator for top level declarations
                              -- used for nested definitions
          ElabInfo annot -> -- elaboration parameters
          Env Term vars -> -- bound names (lambda, pi, let)
          NestedNames vars -> -- locally defined names (arising from nested top level
                              -- declarations)
          (term : RawImp annot) -> -- Term to elaborate
          (expected : ExpType (Term vars)) -> -- Expected type, if available
          Core annot (Term vars, Term vars) 
  -- If we've just inserted an implicit coercion (in practice, that's either
  -- a force or delay) then check the term with any further insertions
  check rigc process elabinfo env nest (ICoerced loc tm) exp
      = checkImp rigc process elabinfo env nest tm exp
  -- If there's local definitions, add implicits inside the block
  check rigc process elabinfo env nest tm@(ILocal loc fs sc) expected
      = checkImp rigc process elabinfo env nest tm expected
  -- No implicits on record updates
  check rigc process elabinfo env nest tm@(IUpdate loc fs rec) expected
      = checkImp rigc process elabinfo env nest tm expected
  check rigc process elabinfo env nest tm@(ILet loc rig n ty val sc) expected
      = checkImp rigc process elabinfo env nest tm expected
  check rigc process elabinfo env nest tm_in exp 
      = do gam <- get Ctxt
           est <- get EST
           let tm = expandAmbigName (elabMode elabinfo) est
                                    gam env nest tm_in [] tm_in exp
           let lazyTm = insertLazy gam tm (map (nf gam env) exp)
           case elabMode elabinfo of
               -- don't expand implicit lambda on LHS
               InLHS _ => checkImp rigc process elabinfo env nest lazyTm exp
               _ => do tm' <- insertImpLam env lazyTm exp 
                       let loc = getAnnot tm'
                       case forceName gam of
                            Nothing => checkImp rigc process elabinfo env nest tm' exp
                            Just fn =>
                               let forcetm = IApp loc (IVar loc fn) 
                                                      (ICoerced loc tm') in
                                   insertForce tm'
                                       (checkImp rigc process elabinfo env nest tm' exp)
                                       (checkImp rigc process elabinfo env nest forcetm exp)

  -- Check a term which is a function to be applied, adding a Force if the term
  -- has a 'Delay' type.
  checkFnApp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
               {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
               {auto m : Ref Meta (Metadata annot)} ->
               Reflect annot =>
               RigCount ->
               Elaborator annot -> -- the elaborator for top level declarations
                                   -- used for nested definitions
               annot ->
               ElabInfo annot -> -- elaboration parameters
               Env Term vars -> -- bound names (lambda, pi, let)
               NestedNames vars -> -- locally defined names (arising from nested top level
                                   -- declarations)
               (term : RawImp annot) -> -- Term to elaborate
               (exp : ExpType (Term vars)) ->
               Core annot (Term vars, Term vars) 
  checkFnApp {vars} rigc process loc elabinfo env nest tm_in exp
      = do defs <- get Ctxt
           handle
             (do log 10 $ "Checking " ++ show tm_in ++ " at " ++ show exp
                 (ctm, cty) <- check rigc process elabinfo env nest tm_in exp
                 log 10 $ "Checked fnapp " ++ show (ctm, cty, exp)
                 let ctynf = nf defs env cty
                 case exp of
                      FnType args ret => 
                           if safeRetTy Z env cty
                              then unifyFnArgs ctynf ctynf (reverse args) ret
                              else log 10 $ "Can't unifyFnArgs for " ++ show cty
                      _ => pure ()
                 case ctynf of
                      NTCon n _ _ _ =>
                          if isDelayType n defs
                             then throw (InternalError "Force")
                             else checkExp rigc process loc elabinfo env nest
                                           ctm cty exp
                      _ => checkExp rigc process loc elabinfo env nest
                                    ctm cty exp)
             (\err =>
                  case err of
                       InternalError "Force" =>
                           case forceName defs of
                                Nothing => check rigc process elabinfo env nest tm_in Unknown
                                Just fn =>
                                   let loc = getAnnot tm_in in
                                       check rigc process elabinfo env nest 
                                         (IApp loc (IVar loc fn)
                                               (ICoerced loc tm_in))
                                         Unknown
                       _ => throw err)
    where
      -- Try to unify the expected return type with the function's return type.
      -- This is in an effort to specialise any of the implicit arguments we've
      -- acquired so far, which might make disambiguation of names in the arguments
      -- easier. If it fails, it might be due to an error elsewhere (or it might
      -- be that there is a dependency in the type we haven't refined yet), in
      -- which case we'll get a more precise error later.

      unifyFnArgs : NF vars -> NF vars -> List (Name, Term vars) -> 
                    Term vars -> Core annot ()
      unifyFnArgs fty topty [] ret
          = do defs <- get Ctxt
               log 2 $ "Converting in fnapp: " ++
                       show (quote defs env topty) ++ " and " ++
                       show ret
               try (do [] <- convert loc (elabMode elabinfo) env topty (nf defs env ret) 
                             | _ => throw (InternalError "No such luck")
                       pure ())
                   (pure ())
      unifyFnArgs (NBind b (Pi c p t) scf) topty ((an, argty) :: args) ret
          = unifyFnArgs (scf (toClosure defaultOpts env Erased)) topty 
                        args (Bind an (Pi c p argty) (weaken ret))
      unifyFnArgs _ _ _ _ = pure ()
      
      -- The above doesn't work if any of the arguments appear in the return 
      -- type, because we have to unify without any assumptions about what the
      -- functions arguments will be.
      -- So, safeRetTy checks for that.
      safeRetTy : Nat -> Env Term vs -> Term vs -> Bool
      safeRetTy n env (Bind _ b sc) = safeRetTy (S n) (b :: env) sc
      safeRetTy Z env tm = True
      safeRetTy n env tm
          = not (any (under n) (findUsedLocs env tm))
        where
          under' : Nat -> Elem x vs -> Bool
          under' Z el = False
          under' (S k) Here = True
          under' (S k) (There p) = under' k p

          under : Nat -> (x ** Elem x vs) -> Bool
          under n (_ ** el) = under' n el

  delayError : Defs -> Error annot -> Bool
  delayError defs ForceNeeded = True
  delayError defs (InType _ _ err) = delayError defs err
  delayError defs (InCon _ _ err) = delayError defs err
  delayError defs (InLHS _ _ err) = delayError defs err
  delayError defs (InRHS _ _ err) = delayError defs err
  delayError _ _ = False

  insertForce : {auto c : Ref Ctxt Defs} -> 
                {auto u : Ref UST (UState annot)} ->
                {auto e : Ref EST (EState vars)} ->
                {auto i : Ref ImpST (ImpState annot)} ->
                {auto m : Ref Meta (Metadata annot)} ->
                RawImp annot ->
                Core annot (Term vars, Term vars) ->
                Core annot (Term vars, Term vars) ->
                Core annot (Term vars, Term vars)
  insertForce orig elab forced
      = do defs <- get Ctxt
           handle elab
               (\err => do defs <- get Ctxt
                           if not (explicitLazy defs (getFn orig))
                              && delayError defs err 
                                then forced else throw err)

  insertLazy : Defs -> RawImp annot -> ExpType (NF vars) -> RawImp annot
  -- If the expected type is "Delayed" and the given term doesn't elaborate
  -- then we'll try inserting a "Delay"
  insertLazy defs tm (FnType [] (NTCon n _ _ args))
      = case delayName defs of
             Nothing => tm
             Just delay =>
                if isDelayType n defs && not (explicitLazy defs (getFn tm))
                   then let loc = getAnnot tm in
                            IAlternative loc FirstSuccess 
                             [IApp loc (IVar loc delay) (ICoerced loc tm), tm]
                   else tm
  insertLazy defs tm _ = tm

  checkImp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
             {auto m : Ref Meta (Metadata annot)} ->
             Reflect annot =>
             RigCount ->
             Elaborator annot ->
             ElabInfo annot ->
             Env Term vars -> NestedNames vars ->
             (term : RawImp annot) -> (expected : ExpType (Term vars)) ->
             Core annot (Term vars, Term vars) 
  checkImp rigc process elabinfo env nest (ICoerced _ tm) expected
      = checkImp rigc process elabinfo env nest tm expected
  checkImp rigc process elabinfo env nest (IVar loc x) expected 
      = case lookup x (names nest) of
             Just (nestn, tm) =>
                  do gam <- get Ctxt
                     let n' = maybe x id nestn
                     case lookupTyExact n' (gamma gam) of
                          Nothing => throw (UndefinedName loc n')
                          Just varty => 
                             do let tyenv = useVars (getArgs tm) (embed varty)
                                (ty_nf, imps) <- getImps rigc process loc env nest elabinfo (nf gam env tyenv) []
                                let ty = if isNil imps 
                                            then tyenv
                                            else quote (noGam gam) env ty_nf
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
      = do n <- case plicity of
                     Explicit => genVarName "arg"
                     Implicit => genVarName "implicit"
                     AutoImplicit => genVarName "con"
           checkPi rigc process elabinfo loc env nest rigp plicity (dropNS n) ty retTy expected
  checkImp rigc process elabinfo env nest (IPi loc rigp plicity (Just n) ty retTy) expected 
      = checkPi rigc process elabinfo loc env nest rigp plicity n ty retTy expected
  checkImp rigc process elabinfo env nest (ILam loc rigl plicity Nothing ty scope) expected
      = do n <- genVarName "lam"
           checkLam (bindRig rigc) process elabinfo loc env nest rigl plicity n ty scope expected
  checkImp rigc process elabinfo env nest (ILam loc rigl plicity (Just n) ty scope) expected
      = checkLam (bindRig rigc) process elabinfo loc env nest rigl plicity n ty scope expected
  checkImp rigc process elabinfo env nest (ILet loc rigl n nTy nVal scope) expected 
      = checkLet (bindRig rigc) process elabinfo loc env nest rigl n nTy nVal scope expected
  checkImp rigc process elabinfo env nest (ICase loc scr scrty alts) expected 
        -- Delay, to collect usage information for linear bindings elsewhere,
        -- which will help build the case type accurately
      = delayElab loc env expected $
          checkCase rigc process elabinfo loc env nest scr scrty alts expected
  checkImp rigc process elabinfo env nest (ILocal loc nested scope) expected 
      = checkLocal rigc process elabinfo loc env nest nested scope expected
  checkImp rigc process elabinfo env nest (IUpdate loc fs rec) expected
      = do recty <- case expected of
                         FnType [] ret => pure ret
                         _ => do (_, ty) <- checkImp rigc process elabinfo 
                                                     env nest rec Unknown
                                 pure ty
           rcase <- recUpdate rigc process elabinfo loc env nest fs rec recty
           log 5 $ "Record update: " ++ show rcase
           check rigc process elabinfo env nest rcase expected
  checkImp {vars} rigc process elabinfo env nest (IApp loc fn arg) expected 
      = do -- Collect the implicits from the top level application first
           let (fn', args) = collectGivenImps fn
           ogam <- get Ctxt
           let elabinfoG = addGivenImps elabinfo args
           -- If we're elaborating a literal, we need to resolve interfaces
           -- even on the LHS, so elaborate in InExpr mode
           let elabinfo' = if isPrimApp ogam
                              then (record { elabMode = InExpr } elabinfoG)
                              else elabinfoG
           log 10 $ "Implicits: " ++ show (implicitsGiven elabinfo')
           (restm, resty) <- checkApp rigc process elabinfo' loc env nest fn' arg expected
           -- Add any remaining implicits greedily
           gam <- get Ctxt
           log 10 $ "Result type: " ++ show (quote gam env (nf gam env resty))
           (ty, imps) <- getImps rigc process loc env nest elabinfo' (nf gam env resty) []
           log 10 $ "Checked app " ++ show (restm, quote (noGam gam) env ty, imps)
           -- Check all of the implicits we collected have been used
           est <- get EST
           log 10 $ "Used: " ++ show (implicitsUsed est, map fst args)
           checkUsedImplicits loc env (elabMode elabinfo) (implicitsUsed est) args 
                              (apply restm imps)
           est <- get EST
           case imps of
                [] => pure (restm, resty)
                _ => do let wantedTm = apply restm imps
                        let wantedTy = quote (noGam gam) env ty
                        checkExp rigc process loc elabinfo env nest wantedTm 
                                   wantedTy expected
    where
      isPrimAppF : (Defs -> Maybe Name) ->
                   Defs -> RawImp annot -> RawImp annot -> Bool
      isPrimAppF pname defs (IVar _ n) (IPrimVal _ _)
          = case pname defs of
                 Nothing => False
                 Just n' => dropNS n == n'
      isPrimAppF pname defs _ _ = False

      isPrimApp : Defs -> Bool
      isPrimApp defs 
          = isPrimAppF fromIntegerName defs fn arg
          || isPrimAppF fromStringName defs fn arg
          || isPrimAppF fromCharName defs fn arg

  checkImp rigc process elabinfo env nest (IImplicitApp loc fn nm arg) expected 
      = do let (fn', args) = collectGivenImps fn
           let elabinfo' = addGivenImps elabinfo ((nm, arg) :: args)
           log 10 $ "IImplicits: " ++ show (implicitsGiven elabinfo')
           (restm, resty) <- check rigc process elabinfo' env nest fn' expected
           -- Add any remaining implicits greedily
           gam <- get Ctxt
           log 10 $ "Result type: " ++ show (quote gam env (nf gam env resty))
           (ty, imps) <- getImps rigc process loc env nest elabinfo' (nf gam env resty) []
           log 10 $ "Checked app " ++ show (restm, quote (noGam gam) env ty, imps)
           -- Check all of the implicits we collected have been used
           est <- get EST
           log 10 $ "IUsed: " ++ show (implicitsUsed est, nm :: map fst args)
           checkUsedImplicits loc env (elabMode elabinfo) (implicitsUsed est) 
                              ((nm, arg) :: args) (apply restm imps)
           case imps of
                [] => pure (restm, resty)
                _ => checkExp rigc process loc elabinfo env nest (apply restm imps) 
                              (quote (noGam gam) env ty) expected
  checkImp rigc process elabinfo env nest (ISearch loc depth) (FnType [] expected)
      = do est <- get EST
           n <- addSearchable loc env expected depth (defining est)
           pure (mkConstantApp n env, expected)
  checkImp rigc process elabinfo env nest (ISearch loc depth) _
      = do est <- get EST
           -- We won't be able to search for this until we know the type,
           -- but make a hole for it anyway and we'll come back to it
           t <- addHole loc env TType "search"
           let expected = mkConstantApp t env
           n <- addSearchable loc env expected depth (defining est)
           log 5 $ "Added search (invented type) for " ++ show expected
           pure (mkConstantApp n env, expected)
  checkImp rigc process elabinfo env nest (IAlternative loc (UniqueDefault def) alts) mexpected
      = do expected <- expty (do t <- addHole loc env TType "alt"
                                 log 5 $ "Added hole for ambiguous expression type (UniqueDefault) " ++ show t
                                 pure (mkConstantApp t env))
                             pure mexpected
           solveConstraints (case elabMode elabinfo of
                                  InLHS c => InLHS
                                  _ => InTerm) Normal
           defs <- get Ctxt
           delayOnFailure loc env expected ambiguous $
            (\delayed =>
               do gam <- get Ctxt
                  let alts' = pruneByType defs (nf defs env expected) alts
                  log 5 $ "Ambiguous elaboration " ++ show alts' ++ 
                          "\nDefault " ++ show def ++
                          "\nTarget type " ++ show (map (normaliseHoles gam env) (Just expected))
                  if delayed -- use the default if there's still ambiguity
                     then try (exactlyOne loc env (elabMode elabinfo) 
                                 (map (\t => 
                                   (getName t, checkImp rigc process elabinfo env nest t
                                       (FnType [] expected))) alts'))
                              (checkImp rigc process elabinfo env nest def
                                     (FnType [] expected))
                     else exactlyOne loc env (elabMode elabinfo) (map (\t => 
                             (getName t, checkImp rigc process elabinfo env nest t 
                                 (FnType [] expected))) alts'))
  checkImp rigc process elabinfo env nest (IAlternative loc uniq alts) mexpected
      = do expected <- expty (do t <- addHole loc env TType "alt"
                                 log 5 $ "Added hole for ambiguous expression type " ++ show t
                                 pure (mkConstantApp t env))
                             pure mexpected
           defs <- get Ctxt
           solveConstraints (case elabMode elabinfo of
                                  InLHS c => InLHS
                                  _ => InTerm) Normal
           delayOnFailure loc env expected ambiguous $
            (\delayed =>
               do gam <- get Ctxt
                  when (not delayed && holeIn (gamma gam) mexpected) $
                    throw (AllFailed [])
                  let alts' = pruneByType defs (nf defs env expected) alts
                  log 5 $ "Ambiguous elaboration " ++ show alts' ++ 
                          "\nTarget type " ++ show (normaliseHoles gam env expected)
                  let tryall = case uniq of
                                    FirstSuccess => anyOne loc
                                    _ => exactlyOne loc env
                  tryall (elabMode elabinfo)
                         (map (\t => (getName t, 
                                       do res <- checkImp rigc process elabinfo env nest t (FnType [] expected)
                                          -- Do it twice for interface resolution;
                                          -- first pass gets the determining argument
                                          -- (maybe rethink this, there should be a better
                                          -- way that allows one pass)
                                          solveConstraints (case elabMode elabinfo of
                                                                 InLHS c => InLHS
                                                                 _ => InTerm) Normal
                                          solveConstraints (case elabMode elabinfo of
                                                                 InLHS c => InLHS
                                                                 _ => InTerm) Normal
                                          log 10 $ show (getName t) ++ " success"
                                          pure res)) alts'))
    where
      holeIn : Gamma -> ExpType (Term vars) -> Bool
      holeIn gam (FnType [] tm)
          = case getFn tm of
                 Ref nt n =>
                      case lookupDefExact n gam of
                           Just (Hole _ pvar _) => not pvar
                           _ => False
                 _ => False
      holeIn gam _ = False

  checkImp {vars} rigc process elabinfo env nest (IRewrite loc rule tm) (FnType [] expected)
        -- if it fails, it may just be that the expected type is not yet
        -- resolved, so come back to it
      = delayOnFailure loc env expected rewriteErr (\delayed =>
          do (rulev, rulet) <- check Rig0 process elabinfo env nest rule Unknown
             (lemma, pred, predty) <- elabRewrite loc env expected rulet

             rname <- genVarName "_"
             pname <- genVarName "_"

             let pbind = Let Rig0 pred predty
             let rbind = Let Rig0 (weaken rulev) (weaken rulet)

             let env' = rbind :: pbind :: env

             -- Nothing we do in this last part will affect the EState,
             -- we're only doing the application this way to make sure the
             -- implicits for the rewriting lemma are in the right place. But,
             -- we still need the right type for the EState, so weaken it once
             -- for each of the let bindings above.
             e' <- weakenedEState
             e'' <- weakenedEState {e = e'}

             (rwtm, rwty) <- check {e = e''} {vars = rname :: pname :: vars}
                                  rigc process elabinfo env' (weaken (weaken nest))
                               (apply (IVar loc lemma) [IVar loc pname,
                                                        IVar loc rname, 
                                                        tm]) 
                               (FnType [] (weakenNs [rname, pname] expected))

             pure (Bind pname pbind (Bind rname rbind rwtm), 
                   Bind pname pbind (Bind rname rbind rwty)))
  checkImp {vars} rigc process elabinfo env nest (IRewrite loc rule tm) _
      = throw (GenericMsg loc "Can't infer a type for rewrite")
  checkImp rigc process elabinfo env nest (IPrimVal loc x) expected 
      = do (x', ty) <- infer loc env (RPrimVal x)
           checkExp rigc process loc elabinfo env nest x' ty expected
  -- TODO: Lift out escaped subterms and elaborate as let bound
  checkImp {vars} rigc process elabinfo env nest (IQuote loc tm) expected
      = do defs <- get Ctxt
           let Just tm' = reflect defs env tm 
                | Nothing => throw (GenericMsg loc "Reflection failed")
           let Just ty = getCon {vars} defs (NS ["Reflect"] (UN "TTImp"))
                | Nothing => throw (InternalError "Reflection failed")
           checkExp rigc process loc elabinfo env nest tm' ty expected
  checkImp rigc process elabinfo env nest (IUnquote loc tm) expected
      = throw (InternalError "Escape should have been resolved before here")
  checkImp rigc process elabinfo env nest (IType loc) exp
      = checkExp rigc process loc elabinfo env nest TType TType exp
  checkImp rigc process elabinfo env nest (IBindVar loc str) topexp
      = do let elabmode = elabMode elabinfo
           -- In types, don't rebind if the name is already in scope;
           -- Below, return True if we don't need to implicitly bind the name
           let False = case implicitMode elabinfo of
                            PI _ => maybe False (const True) (defined (UN str) env)
                            _ => False
                 | _ => checkName rigc process elabinfo loc env nest (UN str) topexp
           est <- get EST
           let n = PV (UN str) (defining est)
           let elabmode = elabMode elabinfo
           noteLHSPatVar elabmode str
           notePatVar n
           est <- get EST
           case lookup n (boundNames est) of
                Nothing =>
                  do (tm, exp) <- mkOuterHole loc n True env topexp
                     log 5 $ "Added Bound implicit " ++ show (n, (tm, exp))
                     defs <- get Ctxt
                     log 10 $ show (lookupDefExact n (gamma defs))
                     est <- get EST
                     put EST 
                         (record { boundNames $= ((n, (tm, exp)) ::),
                                   toBind $= ((n, (tm, exp)) :: ) } est)
                     addNameType loc (UN str) env exp
                     checkExp rigc process loc elabinfo env nest tm exp topexp
                Just (tm, ty) =>
                  do addNameType loc (UN str) env ty
                     checkExp rigc process loc elabinfo env nest tm ty topexp
  checkImp rigc process elabinfo env nest (IBindHere loc tm) expected
      = do est <- get EST
           let oldenv = outerEnv est
           let oldsub = subEnv est
           let oldbif = bindIfUnsolved est
           let dontbind = map fst (toBind est)
           -- Set the binding environment in the elab state - unbound
           -- implicits should have access to whatever is in scope here
           put EST (updateEnv env SubRefl [] est)
           (tmv, tmt) <- check rigc process elabinfo env nest tm expected
           solveConstraints (case elabMode elabinfo of
                                  InLHS c => InLHS
                                  _ => InTerm) Normal
           argImps <- getToBind loc 
                                (elabMode elabinfo)
                                (implicitMode elabinfo)
                                env dontbind tmv
           clearToBind dontbind
           gam <- get Ctxt
           est <- get EST
           put EST (updateEnv oldenv oldsub oldbif 
                       (record { boundNames = [] } est))
           let (bv, bt) = bindImplicits (implicitMode elabinfo)
                                        gam env argImps (asVariables est)
                                        (normaliseHoles gam env tmv)
                                        TType
           traverse implicitBind (map fst argImps)
           checkExp rigc process loc elabinfo env nest bv bt expected
  checkImp rigc process elabinfo env nest (IMustUnify loc r tm) (FnType [] expected) with (elabMode elabinfo)
    checkImp rigc process elabinfo env nest (IMustUnify loc r tm) (FnType [] expected) | (InLHS _)
      = do (wantedTm, wantedTy) <- checkImp rigc process 
                                            (record { dotted = True,
                                                      elabMode = InExpr } elabinfo)
                                            env nest tm (FnType [] expected)
           n <- addHole loc env expected "dot"
           gam <- getCtxt
           let tm = mkConstantApp n env
           log 10 $ "Added hole for MustUnify " ++ show (tm, wantedTm, wantedTy)
           addDot loc env n wantedTm r tm
           checkExp rigc process loc (record { elabMode = InExpr } elabinfo) 
                    env nest tm wantedTy (FnType [] expected)
    checkImp rigc process elabinfo env nest (IMustUnify loc r tm) (FnType [] expected) | elabmode
        = throw (GenericMsg loc ("Dot pattern not valid here (not LHS)" ++ show tm))
  checkImp rigc process elabinfo env nest (IMustUnify loc r tm) expected
      = throw (GenericMsg loc ("Dot pattern not valid here (unknown type) " ++ show tm))
  checkImp rigc process elabinfo env nest (IAs loc var tm) expected with (elabMode elabinfo)
    checkImp rigc process elabinfo env nest (IAs loc var tm) (FnType [] expected) | (InLHS c)
      = checkAs rigc process elabinfo loc env nest var tm expected
    checkImp rigc process elabinfo env nest (IAs loc var tm) expected | elabmode
        = throw (GenericMsg loc "@-pattern not valid here")
  checkImp rigc process elabinfo env nest (IHole loc n_in) (FnType [] expected) 
      = do n <- inCurrentNS (UN n_in)
           -- Let to lambda as above
           let env' = letToLam env
           addNamedHole loc n False env' expected
           -- Record the lhs for this hole in the metadata
           withCurrentLHS n
           est <- get EST
           put EST (record { holesMade $= (n ::) } est)
           pure (mkConstantApp n env', expected)
  checkImp rigc process elabinfo env nest (IHole loc n_in) _
      = do t <- addHole loc env TType "ty"
           -- Turn lets into lambda before making the hole so that they
           -- get abstracted over in the hole (it's fine here, unlike other
           -- holes, because we're not trying to unify it so it's okay if
           -- applying the metavariable isn't a pattern form)
           let env' = letToLam env
           let hty = mkConstantApp t env'
           n <- inCurrentNS (UN n_in)
           addNamedHole loc n False env' hty
           -- Record the lhs for this hole in the metadata
           withCurrentLHS n
           est <- get EST
           put EST (record { holesMade $= (n ::) } est)
           pure (mkConstantApp n env', hty)
  checkImp rigc process elabinfo env nest (Implicit loc) (FnType [] expected) 
      = do n <- addHole loc env expected "_"
           log 10 $ "Added hole for implicit " ++ show (n, expected, mkConstantApp n env)
           est <- get EST
           let tm = mkConstantApp n env
           put EST (addBindIfUnsolved n env tm expected est)
           pure (tm, expected)
  checkImp rigc process elabinfo env nest (Implicit loc) _
      = do t <- addHole loc env TType "impty"
           let hty = mkConstantApp t env
           n <- addHole loc env hty "_"
           log 10 $ "Added hole for implicit type " ++ show n
           pure (mkConstantApp n env, hty)
  checkImp rigc process elabinfo env nest (Infer loc) (FnType [] expected) 
      = do n <- addHole loc env expected "_"
           log 10 $ "Added hole for implicit " ++ show (n, expected, mkConstantApp n env)
           pure (mkConstantApp n env, expected)
  checkImp rigc process elabinfo env nest (Infer loc) _
      = do t <- addHole loc env TType "impty"
           let hty = mkConstantApp t env
           n <- addHole loc env hty "_"
           log 10 $ "Added hole for implicit type " ++ show n
           pure (mkConstantApp n env, hty)

  addGivenImps : ElabInfo annot -> List (Maybe Name, RawImp annot) -> ElabInfo annot
  addGivenImps elabinfo ns = record { implicitsGiven $= (ns ++) } elabinfo

  -- Check a name. At this point, we've already established that it's not
  -- one of the local definitions, so it either must be a local variable or
  -- a globally defined name
  checkName : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
              {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
              {auto m : Ref Meta (Metadata annot)} ->
              Reflect annot =>
              RigCount -> Elaborator annot -> ElabInfo annot -> annot -> Env Term vars -> 
              NestedNames vars -> Name -> ExpType (Term vars) ->
              Core annot (Term vars, Term vars)
  checkName {vars} rigc process elabinfo loc env nest x expected 
      = do gam <- get Ctxt
           case defined x env of
             Just (rigb, lv) => 
                 do rigSafe rigb rigc
                    est <- get EST
                    when (isLinear rigb && rigc /= Rig1 True) $
                         put EST 
                             (record { linearUsed $= ((_ ** lv) :: ) } est)
                    let varty = binderType (getBinder lv env) 
                    log 5 $ "Getting implicits " ++ show varty ++ " for " ++ show expected
                    (ty, imps) <- getImps rigc process loc env nest elabinfo (nf gam env varty) []
                    let tytm = if isNil imps
                                  then varty
                                  else quote (noGam gam) env ty
                    addNameType loc (dropNS x) env tytm
                    checkExp rigc process loc elabinfo env nest 
                         (apply (Local (Just rigb) lv) imps) tytm expected
             Nothing =>
                 do nspace <- getNS
                    case lookupGlobalNameIn nspace x (gamma gam) of
                         [] => throw $ UndefinedName loc x
                         [(fullname, gdef)] => 
                              do let ty = type gdef
                                 let def = definition gdef
                                 let mult = multiplicity gdef
                                 resolveRef fullname gdef gam
                         ns => exactlyOne loc env (elabMode elabinfo)
                                    (map (\ (n, gdef) =>
                                       (Just n, resolveRef n gdef gam)) ns)
    where
      rigSafe : RigCount -> RigCount -> Core annot ()
      rigSafe (Rig1 b) RigW = throw (LinearMisuse loc x (Rig1 b) RigW)
      rigSafe Rig0 RigW = throw (LinearMisuse loc x Rig0 RigW)
      rigSafe Rig0 (Rig1 b) = throw (LinearMisuse loc x Rig0 (Rig1 b))
      rigSafe _ _ = pure ()

      defOK : Bool -> ElabMode -> NameType -> Bool
      defOK False (InLHS _) (DataCon _ _) = True
      defOK False (InLHS _) _ = False
      defOK _ _ _ = True

      checkVisibleNS : Name -> Core annot ()
      checkVisibleNS (NS ns x)
          = if !(isVisible ns)
               then pure ()
               else do defs <- get Ctxt
                       throw $ InvisibleName loc (NS ns x)
      checkVisibleNS _ = pure ()

      resolveRef : Reflect annot =>
                   Name -> GlobalDef -> Defs ->
                   Core annot (Term vars, Term vars)
      resolveRef n gdef gam
          = do let varty = embed (type gdef)
               let def = definition gdef
               let mult = multiplicity gdef
               rigSafe mult rigc
               checkVisibleNS n
               let nt : NameType 
                        = case def of
                             PMDef _ _ _ _ _ => Func
                             DCon tag arity _ => DataCon tag arity
                             TCon tag arity _ _ _ _ => TyCon tag arity
                             _ => Func
               log 5 $ "Getting implicits " ++ show varty ++ " for " ++ show expected
               (ty, imps) <- getImps rigc process loc env nest elabinfo (nf gam env varty) []
               if topLevel elabinfo ||
                    defOK (dotted elabinfo) (elabMode elabinfo) nt
                  then do let tytm = if isNil imps
                                        then varty
                                        else quote (noGam gam) env ty
                          addNameType loc (dropNS x) env tytm
                          checkExp rigc process loc elabinfo env nest 
                                       (apply (Ref nt n) imps) 
                                       tytm expected
                  else throw (BadPattern loc n)

  -- TODO: There's a lot of this, the components probably belongs in 
  -- their own module
  checkCase : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
              {auto e : Ref EST (EState vars)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              {auto m : Ref Meta (Metadata annot)} ->
              Reflect annot =>
              RigCount -> Elaborator annot ->
              ElabInfo annot -> annot -> Env Term vars -> NestedNames vars -> 
              RawImp annot -> RawImp annot -> List (ImpClause annot) ->
              ExpType (Term vars) ->
              Core annot (Term vars, Term vars)
  checkCase rigc process elabinfo loc env nest scr scrty_exp alts expected
      = do (scrtyv, scrtyt) <- check Rig0 process elabinfo env nest scrty_exp 
                                     (FnType [] TType)
           log 10 $ "Expected scrutinee type: " ++ show scrtyv
           -- Try checking at the given multiplicity; if that doesn't work,
           -- try checking at Rig1 (meaning that we're using a linear variable
           -- so the scrutinee should be linear)
           (scrtm_in, scrty, caseRig) <- handle
              (do c <- check RigW process elabinfo env nest scr (FnType [] scrtyv)
                  pure (fst c, snd c, RigW))
              (\err => case err of
                            LinearMisuse _ _ (Rig1 x) _
                              => do c <- check rig1 process elabinfo env nest scr 
                                               (FnType [] scrtyv)
                                    pure (fst c, snd c, rig1)
                            e => throw e)
           caseBlock rigc process elabinfo loc env nest scr scrtm_in scrty caseRig alts expected

  checkLocal : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
               {auto e : Ref EST (EState vars)} ->
               {auto i : Ref ImpST (ImpState annot)} ->
               {auto m : Ref Meta (Metadata annot)} ->
               Reflect annot =>
               RigCount -> Elaborator annot ->
               ElabInfo annot -> annot -> Env Term vars -> NestedNames vars -> 
               List (ImpDecl annot) -> RawImp annot ->
               ExpType (Term vars) ->
               Core annot (Term vars, Term vars)
  checkLocal {vars} {c} {u} {i} {m} rigc process elabinfo loc env nest nested scope expected
      = do let defNames = definedInBlock nested
           est <- get EST
           let f = defining est
           let nest' = record { names $= ((map (applyEnv f) defNames) ++) } nest
           let env' = dropLinear env
           traverse (process c u i m False env' nest') (map (updateName nest') nested)
           check rigc process elabinfo env nest' scope expected
    where
      -- For the local definitions, don't allow access to linear things
      -- unless they're explicitly passed.
      -- This is because, at the moment, we don't have any mechanism of
      -- ensuring the nested definition is used exactly once
      dropLinear : Env Term vs -> Env Term vs
      dropLinear [] = []
      dropLinear (b :: bs) 
          = if isLinear (multiplicity b)
               then setMultiplicity b Rig0 :: dropLinear bs
               else b :: dropLinear bs

      applyEnv : Name -> Name -> (Name, (Maybe Name, Term vars))
      applyEnv outer inner = (inner, (Just (GN (Nested outer inner)), 
                                      mkConstantAppFull (GN (Nested outer inner)) env))

      -- Update the names in the declarations to the new 'nested' names.
      -- When we encounter the names in elaboration, we'll update to an
      -- application of the nested name.
      newName : NestedNames vars -> Name -> Name
      newName nest n 
          = case lookup n (names nest) of
                 Just (Just n', _) => n'
                 _ => n

      updateTyName : NestedNames vars -> ImpTy annot -> ImpTy annot
      updateTyName nest (MkImpTy loc' n ty) 
          = MkImpTy loc' (newName nest n) ty

      updateDataName : NestedNames vars -> ImpData annot -> ImpData annot
      updateDataName nest (MkImpData loc' n tycons dopts dcons)
          = MkImpData loc' (newName nest n) tycons dopts
                           (map (updateTyName nest) dcons)
      updateDataName nest (MkImpLater loc' n tycons)
          = MkImpLater loc' (newName nest n) tycons

      updateName : NestedNames vars -> ImpDecl annot -> ImpDecl annot
      updateName nest (IClaim loc' r vis fnopts ty) 
           = IClaim loc' r vis fnopts (updateTyName nest ty)
      updateName nest (IDef loc' n cs) 
           = IDef loc' (newName nest n) cs
      updateName nest (IData loc' vis d) 
           = IData loc' vis (updateDataName nest d)
      updateName nest i = i

  checkAs : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            {auto m : Ref Meta (Metadata annot)} ->
            Reflect annot =>
            RigCount -> Elaborator annot ->
            ElabInfo annot -> annot -> Env Term vars -> NestedNames vars -> 
            Name -> (arg : RawImp annot) ->
            Term vars ->
            Core annot (Term vars, Term vars) 
  checkAs rigc process elabinfo loc env nest var tm expected
      = do est <- get EST
           let n = PV var (defining est)
           (patTm, patTy) <- checkImp rigc process elabinfo env nest tm (FnType [] expected)
           notePatVar n
           est <- get EST
           case lookup n (boundNames est) of
                Just (tm, ty) =>
                    throw (GenericMsg loc ("Name " ++ show var ++ " already bound"))
                Nothing =>
                    do tm <- addBoundName loc n False env expected
                       log 5 $ "Added @ pattern name " ++ show (n, (tm, expected))
                       put EST
                           (record { boundNames $= ((n, (tm, expected)) ::),
                                     toBind $= ((n, (tm, expected)) ::),
                                     asVariables $= ((n, asRig rigc) ::) } est)
                       gam <- get Ctxt
                       -- Unify the given expression with the as pattern hole.
                       -- This will resolve the as pattern hole with the
                       -- pattern, which gets let-bound later
                       convert loc (elabMode elabinfo) env (nf gam env tm) (nf gam env patTm)
                       pure (patTm, expected)
    where
      asRig : RigCount -> RigCount
      asRig RigW = RigW
      asRig _ = Rig0 -- can't use if matching on it

  checkApp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             {auto m : Ref Meta (Metadata annot)} ->
             Reflect annot =>
             RigCount -> Elaborator annot ->
             ElabInfo annot -> annot -> Env Term vars -> NestedNames vars -> 
             (fn : RawImp annot) -> (arg : RawImp annot) ->
             ExpType (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkApp {vars} rigc process elabinfo loc env nest fn arg expected
      = do argn <- genVarName "argn"
           (fntm, fnty) <- checkFnApp rigc process loc elabinfo env nest fn 
                                      (case expected of
                                            Unknown => Unknown
                                            FnType args ret => 
                                                FnType ((argn, Erased) :: args) ret)
           gam <- get Ctxt
           case elabMode elabinfo of
                InLHS _ => pure ()
                _ => solveConstraints InTerm Normal
           case nf gam env fnty of
                NBind _ (Pi rigf _ ty) scdone =>
                  do impsUsed <- saveImps
                     let argRig = rigMult rigf rigc
                     -- Can't pattern match on arguments at Rig0
                     let arg' = case (elabMode elabinfo, arg, argRig) of
                                     (_, IBindVar _ _, _) => arg
                                     (_, Implicit _, _) => arg
                                     (_, IAs _ _ (IBindVar _ _), _) => arg
                                     (_, IAs _ _ (Implicit _), _) => arg
                                     (_, IMustUnify _ _ _, _) => arg
-- For the moment: allow erased constructors to appear here, and check
-- when building the case tree. It would be better to have the check here,
-- but it's fiddly to add. In general, it's okay to match on an erased thing
-- if it's value can be determined from other arguments, which means that it's
-- either solvable by unification, or an instance of a collapsible type
-- reconstructed from other non-erased arguments.
--                                      (InLHS (Rig1 _), _, Rig0) => IMustUnify loc "Erased argument" arg
                                     _ => arg
                     -- if the argument is borrowed, it's okay to use it in
                     -- unrestricted context, because we'll be out of the
                     -- application without spending it
                     let checkRig = case (rigf, rigc) of
                                         (Rig1 True, Rig0) => Rig0
                                         (Rig1 True, _) => Rig1 True
                                         _ => rigMult rigf rigc
                     log 5 $ "Checking argument of type " ++ show (quote (noGam gam) env ty)
                                 ++ " at " ++ show checkRig
                     (argtm, argty) <- check checkRig
                                             process (record { implicitsGiven = [] } elabinfo)
                                             env nest arg' 
                                             (FnType [] (quote (noGam gam) env ty))
                     -- Check the result converts with the name we invented earlier
--                      (argtm, argty) <- checkExp rigc process loc elabinfo env nest
--                                                 argtm aty (FnType [] argty)

                     gam <- get Ctxt
                     restoreImps impsUsed
                     let sc' = scdone (toClosure defaultOpts env argtm)
                     log 10 $ "Scope type " ++ show (quote (noGam gam) env sc')
                     checkExp rigc process loc elabinfo env nest (App fntm argtm)
                                  (quote gam env sc') expected
                _ => 
                  do bn <- genVarName "aTy"
                     -- create a hole for the return type
                     log 5 $ "Inventing return type for " ++ show (fn, fnty)
                     atyn <- genName "arg_type"
                     aty <- addBoundName loc atyn False env TType
                     scn <- genName "res_type"
                     scty_in <- addBoundName loc scn False env TType
                     let scty = weaken {n=bn} scty_in

--                      (expty, scty) <- inventFnType loc env bn

                     -- Check the argument type against the invented arg type
                     impsUsed <- saveImps
                     (argtm, argty) <- check rigc process (record { implicitsGiven = [] } elabinfo)
                                             env nest arg (FnType [] aty)
                     restoreImps impsUsed
                     -- Check the type of 'fn' is an actual function type
                     gam <- get Ctxt
                     (fnchk, _) <-
                         checkExp rigc process loc elabinfo env nest fntm 
                                  (Bind bn (Pi RigW Explicit aty) scty) 
                                  (FnType [] (quote gam env fnty))
                     checkExp rigc process loc elabinfo env nest (App fnchk argtm)
                                  (Bind bn (Let RigW argtm argty) scty) expected

  checkPi : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            {auto m : Ref Meta (Metadata annot)} ->
            Reflect annot =>
            RigCount -> Elaborator annot -> ElabInfo annot ->
            annot -> Env Term vars -> NestedNames vars -> RigCount -> PiInfo -> Name -> 
            (argty : RawImp annot) -> (retty : RawImp annot) ->
            ExpType (Term vars) ->
            Core annot (Term vars, Term vars) 
  checkPi rigc process elabinfo loc env nest rigf info n argty retty expected
      = do let impmode = implicitMode elabinfo
           let elabmode = elabMode elabinfo
           (tyv, tyt) <- check Rig0 process (record { topLevel = False } elabinfo) 
                               env nest argty (FnType [] TType)
           let env' : Env Term (n :: _) = Pi RigW info tyv :: env
           est <- get EST
           
           e' <- weakenedEState 
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} Rig0 process elabinfo env' 
                                     (weaken nest') retty (FnType [] TType)
           st' <- strengthenedEState {e=e'} False loc env'
           put EST st'
           checkExp rigc process loc elabinfo env nest (Bind n (Pi rigf info tyv) scopev)
                    TType expected

  checkLam : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             {auto m : Ref Meta (Metadata annot)} ->
             Reflect annot =>
             RigCount -> Elaborator annot -> ElabInfo annot ->
             annot -> Env Term vars -> NestedNames vars -> RigCount -> PiInfo -> Name ->
             (ty : RawImp annot) -> (scope : RawImp annot) ->
             ExpType (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkLam rigc_in process elabinfo loc env nest rigl plicity n ty scope (FnType [] (Bind bn (Pi c Explicit pty) psc))
      = do let rigc = if rigc_in == Rig0 then Rig0 else rig1
           (tyv, tyt) <- check Rig0 process (record { topLevel = False } elabinfo) 
                               env nest ty (FnType [] TType)
           e' <- weakenedEState
           let rigb = min rigl c
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           let env' = Lam rigb plicity tyv :: env
           (scopev, scopet) <- check rigc process {e=e'} 
                                     (record { topLevel = False } elabinfo) env'
                                     (weaken nest') scope 
                                     (FnType [] (renameTop n psc))
           st' <- strengthenedEState False loc env'
           put EST st'
           checkExp rigc process loc elabinfo env nest 
                        (Bind n (Lam rigb plicity tyv) scopev)
                        (Bind n (Pi rigb plicity tyv) scopet)
                        (FnType [] (Bind bn (Pi rigb plicity pty) psc))
  checkLam rigc_in process elabinfo loc env nest rigl plicity n ty scope expected
      = do let rigc = if rigc_in == Rig0 then Rig0 else rig1
           (tyv, tyt) <- check Rig0 process (record { topLevel = False } elabinfo) 
                               env nest ty (FnType [] TType)
           let rigb = rigl -- rigMult rigl rigc
           let env' : Env Term (n :: _) = Lam rigb plicity tyv :: env
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} rigc process 
                                     (record { topLevel = False } elabinfo) 
                                     env' (weaken nest') scope (dropArg expected)
           st' <- strengthenedEState False loc env'
           put EST st'
           checkExp rigc process loc elabinfo env nest (Bind n (Lam rigb plicity tyv) scopev)
                        (Bind n (Pi rigb plicity tyv) scopet)
                        expected
    where
      dropArg : ExpType (Term vars) -> ExpType (Term (x :: vars))
      dropArg Unknown = Unknown
      dropArg (FnType (a :: as) ret) 
         = FnType (map (\ (x, t) => (x, weaken t)) as) (weaken ret)
      dropArg (FnType _ _) = Unknown

  checkLet : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             {auto m : Ref Meta (Metadata annot)} ->
             Reflect annot =>
             RigCount -> Elaborator annot ->
             ElabInfo annot -> annot -> Env Term vars -> NestedNames vars ->
             RigCount -> Name -> 
             (ty : RawImp annot) -> 
             (val : RawImp annot) -> 
             (scope : RawImp annot) ->
             ExpType (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkLet rigc_in process elabinfo loc env nest rigl n ty val scope expected
      = do let rigc = if rigc_in == Rig0 then Rig0 else rig1
           (tyv, tyt) <- check Rig0 process (record { topLevel = False } elabinfo) 
                               env nest ty (FnType [] TType)
           -- Try checking at the given multiplicity; if that doesn't work,
           -- try checking at Rig1 (meaning that we're using a linear variable
           -- so the resulting binding should be linear)
           (valv, valt, rigb) <- handle
                (do c <- check (rigMult rigl rigc) process elabinfo 
                               env nest val (FnType [] tyv)
                    pure (fst c, snd c, rigMult rigl rigc))
                (\err => case err of
                              LinearMisuse _ _ (Rig1 x) _
                                => do c <- check rig1 process 
                                                 (record { topLevel = False } elabinfo) 
                                                 env nest val (FnType [] tyv)
                                      pure (fst c, snd c, rig1)
                              e => throw e)
           let env' : Env Term (n :: _) = Let rigb valv tyv :: env
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} rigc process 
                                     (record { topLevel = False } elabinfo) env' 
                                     (weaken nest') scope (map weaken expected)
           st' <- strengthenedEState (topLevel elabinfo) loc env'
           put EST st'
           checkExp rigc process loc elabinfo env nest
                            (Bind n (Let rigb valv tyv) scopev)
                            (Bind n (Let rigb valv tyv) scopet)
                            expected

  makeImplicit 
          : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
            {auto m : Ref Meta (Metadata annot)} ->
            Reflect annot =>
            RigCount -> Elaborator annot -> annot -> Env Term vars -> NestedNames vars ->
            ElabInfo annot -> Name -> (ty : NF vars) ->
            Core annot (Term vars) 
  makeImplicit rigc process loc env nest elabinfo bn ty
      = case lookup (Just bn) (lamImplicits elabinfo ++ implicitsGiven elabinfo) of
             Just rawtm => 
               do gam <- get Ctxt
                  log 10 $ "Checking implicit " ++ show bn ++ " = " ++ show rawtm
                            ++ " at " ++ show rigc
                            ++ " type " ++ show (quote (noGam gam) env ty)
                  usedImp (Just bn)
                  impsUsed <- saveImps
                  (imptm, impty) <- check rigc process (record { implicitsGiven = [] } elabinfo)
                                          env nest rawtm (FnType [] (quote (noGam gam) env ty))
                  restoreImps impsUsed
                  pure imptm
             Nothing =>
               do gam <- get Ctxt
                  hn <- genName (nameRoot bn)
                  let ty' = quote (noGam gam) env ty
                  log 5 $ "Added implicit argument " ++ show hn ++ " : " ++ show ty'
                  addNamedHole loc hn False env ty'
                  est <- get EST
                  let tm = mkConstantApp hn env
                  put EST (addBindIfUnsolved hn env tm ty' est)
                  pure tm

  lookupAuto : Name -> List (Maybe Name, a) -> Maybe (Maybe Name, a)
  lookupAuto n [] = Nothing
  lookupAuto n ((Nothing, v) :: vs) = Just (Nothing, v) -- first auto implicit
  lookupAuto n ((Just n', v) :: vs)
      = if n == n' then Just (Just n', v) else lookupAuto n vs

  makeAutoImplicit 
          : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
            {auto m : Ref Meta (Metadata annot)} ->
            Reflect annot =>
            RigCount -> Elaborator annot -> annot -> Env Term vars -> NestedNames vars ->
            ElabInfo annot -> Name -> (ty : NF vars) ->
            Core annot (Term vars) 
  makeAutoImplicit rigc process loc env nest elabinfo bn ty
      = case lookupAuto bn (implicitsGiven elabinfo) of
             Just (used, rawtm) =>
               do gam <- get Ctxt
                  usedImp used
                  impsUsed <- saveImps
                  (imptm, impty) <- checkImp rigc process (record { implicitsGiven = [] } elabinfo)
                                             env nest rawtm (FnType [] (quote (noGam gam) env ty))
                  restoreImps impsUsed
                  pure imptm
             Nothing => 
               -- on the LHS, just treat it as an implicit pattern variable.
               -- on the RHS, add a searchable hole
               case elabMode elabinfo of
                    InLHS _ => 
                       do gam <- get Ctxt
                          hn <- genName (nameRoot bn)
                          -- Add as a pattern variable, but let it unify with other
                          -- things, hence 'False' as an argument to addBoundName
                          let expected = quote (noGam gam) env ty
                          tm <- addBoundName loc hn False env expected
                          log 5 $ "Added Bound implicit (makeAutoImplicit) " ++ show (hn, (tm, expected))
                          est <- get EST
                          put EST (record { boundNames $= ((hn, (tm, expected)) :: ),
                                            toBind $= ((hn, (tm, expected)) :: ) } est)
                          pure tm
                    _ => 
                       do gam <- get Ctxt
                          est <- get EST
                          n <- addSearchable loc env (quote (noGam gam) env ty) 500
                                             (defining est)
                          log 5 $ "Initiate search: " ++ show n ++
                                  " for " ++ show (quote (noGam gam) env ty)
                          pure (mkConstantApp n env)

  -- Get the implicit arguments that need to be inserted at this point
  -- in a function application. Do this by reading off implicit Pis
  -- in the expected type ('ty') and adding new holes for each.
  -- Return the (normalised) remainder of the type, and the list of
  -- implicits added
  getImps : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
            {auto m : Ref Meta (Metadata annot)} ->
            Reflect annot =>
            RigCount -> Elaborator annot -> annot -> Env Term vars -> NestedNames vars ->
            ElabInfo annot ->
            (ty : NF vars) -> List (Term vars) ->
            Core annot (NF vars, List (Term vars)) 
  getImps rigc process loc env nest elabinfo (NBind bn (Pi c Implicit ty) sc) imps
      = do tm <- makeImplicit (rigMult rigc c) process loc env nest elabinfo bn ty
           getImps rigc process loc env nest elabinfo 
                   (sc (toClosure defaultOpts env tm)) (tm :: imps)
  getImps rigc process loc env nest elabinfo (NBind bn (Pi c AutoImplicit ty) sc) imps
      = do tm <- makeAutoImplicit (rigMult rigc c) process loc env nest elabinfo bn ty
           getImps rigc process loc env nest elabinfo 
                   (sc (toClosure defaultOpts env tm)) (tm :: imps)
  getImps rigc process loc env nest elabinfo ty imps = pure (ty, reverse imps)

  -- When converting, add implicits until we've applied enough for the
  -- expected type.
  -- Also, if the type we've got is a Delay, and the type we expect isn't,
  -- note that we need a force (we'll handle the error in 'insertForce')
  convertImps : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
                {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
                {auto m : Ref Meta (Metadata annot)} ->
                Reflect annot =>
                RigCount -> Elaborator annot -> annot -> Env Term vars ->
                NestedNames vars -> ElabInfo annot ->
                (got : NF vars) -> (exp : NF vars) -> List (Term vars) ->
                Core annot (NF vars, List (Term vars))
  convertImps rigc process loc env nest elabinfo (NBind bn (Pi c Implicit ty) sc) (NBind bn' (Pi c' Implicit ty') sc') imps
      = pure (NBind bn (Pi c Implicit ty) sc, reverse imps)
  convertImps rigc process loc env nest elabinfo (NBind bn (Pi c AutoImplicit ty) sc) (NBind bn' (Pi c' AutoImplicit ty') sc') imps
      = pure (NBind bn (Pi c AutoImplicit ty) sc, reverse imps)
  convertImps rigc process loc env nest elabinfo (NBind bn (Pi c Implicit ty) sc) exp imps
      = do defs <- get Ctxt
           log 10 $ "Making an implicit for " ++ show (quote (noGam defs) env (sc (toClosure defaultOpts env Erased))) ++ 
                    " and " ++ show (quote (noGam defs) env exp)
           tm <- makeImplicit (rigMult rigc c) process loc env nest elabinfo bn ty
           convertImps rigc process loc env nest elabinfo 
                       (sc (toClosure defaultOpts env tm)) exp (tm :: imps)
  convertImps rigc process loc env nest elabinfo (NBind bn (Pi c AutoImplicit ty) sc) exp imps
      = do tm <- makeAutoImplicit (rigMult rigc c) process loc env nest elabinfo bn ty
           convertImps rigc process loc env nest elabinfo 
                       (sc (toClosure defaultOpts env tm)) exp (tm :: imps)
  convertImps rigc process loc env nest elabinfo got@(NTCon n _ _ args) exp@(NTCon n' _ _ args') imps
      = do defs <- get Ctxt
           if isDelayType n defs 
              then if isDelayType n' defs
                      then pure (got, reverse imps)
                      else throw ForceNeeded
              else pure (got, reverse imps)
  convertImps rigc process loc env nest elabinfo got@(NTCon n _ _ args) exp imps
      = do defs <- get Ctxt
           if isDelayType n defs 
              then throw ForceNeeded
              else pure (got, reverse imps)
  convertImps rigc process loc env nest elabinfo got exp imps = pure (got, reverse imps)

  checkExp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
             {auto m : Ref Meta (Metadata annot)} ->
             Reflect annot =>
             RigCount -> Elaborator annot -> annot -> ElabInfo annot -> Env Term vars ->
             NestedNames vars ->
             (term : Term vars) -> (got : Term vars) -> 
             (exp : ExpType (Term vars)) ->
             Core annot (Term vars, Term vars) 
  checkExp rigc process loc elabinfo env nest tm got (FnType [] exp) 
      = do gam <- get Ctxt
           log 10 $ "Checking conversion " ++ show got ++ " and " ++ show exp
           let expnf = nf gam env exp
           (got', imps) <- convertImps rigc process loc env nest elabinfo (nf gam env got) expnf []
           constr <- convert loc (elabMode elabinfo) env got' expnf
           case constr of
                [] => pure (apply tm imps, quote (noGam gam) env got')
                cs => do gam <- get Ctxt
                         c <- addConstant loc env (apply tm imps) exp cs
                         dumpConstraints 4 False
                         pure (mkConstantApp c env, quote (noGam gam) env got')
  checkExp rigc process loc elabinfo env nest tm got _
      = do gam <- get Ctxt
           pure (tm, got)

