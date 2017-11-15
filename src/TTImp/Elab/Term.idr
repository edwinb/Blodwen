module TTImp.Elab.Term

import TTImp.TTImp
import public TTImp.Elab.State
import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT
import Core.Typecheck
import Core.Unify

import Data.List
import Data.List.Views

%default covering

-- Check a name. At this point, we've already established that it's not
-- one of the local definitions, so it either must be a local variable or
-- a globally defined name
checkName : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            ElabMode -> annot -> Env Term vars -> Name -> Maybe (Term vars) ->
            Core annot (Term vars, Term vars)
checkName {vars} elabmode loc env x expected 
    = do gam <- getCtxt
         case defined x env of
           Just lv => 
               do let varty = binderType (getBinder lv env) 
                  (ty, imps) <- getImps loc env (nf gam env varty) []
                  checkExp loc elabmode env (apply (Local lv) imps)
                          (quote empty env ty) expected
           Nothing =>
               case lookupDefTyName x gam of
                    [] => throw $ UndefinedName loc x
                    [(fullname, def, ty)] => 
                         resolveRef fullname def gam (embed ty)
                    -- TODO: Resolve ambiguities
                    ns => throw $ AmbiguousName loc (map fst ns)
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
             (ty, imps) <- getImps loc env (nf gam env varty) []
             checkExp loc elabmode env (apply (Ref nt n) imps) 
                          (quote empty env ty) expected

mutual
  export
  check : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
          {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
          Elaborator annot ->
          (top : Bool) -> -- top level, unbound implicits bound here
          ImplicitMode -> ElabMode ->
          Env Term vars -> NestedNames vars ->
          (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
          Core annot (Term vars, Term vars) 
  check process top impmode InLHS env nest tm exp -- don't expand implicit lambda on LHS
      = checkImp process top impmode InLHS env nest tm exp
  check process top impmode elabmode env nest tm exp 
      = let tm' = insertImpLam env tm exp in
            checkImp process top impmode elabmode env nest tm' exp

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

  checkImp : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} -> {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             (top : Bool) -> -- top level, unbound implicits bound here
             ImplicitMode -> ElabMode ->
             Env Term vars -> NestedNames vars ->
             (term : RawImp annot) -> (expected : Maybe (Term vars)) ->
             Core annot (Term vars, Term vars) 
  checkImp process top impmode elabmode env nest (IVar loc x) expected 
      = case lookup x (names nest) of
             Just (n', tm) =>
                  do gam <- getCtxt
                     case lookupTyExact n' gam of
                          Nothing => throw (UndefinedName loc n')
                          Just ty => 
                             let tyenv = useVars (getArgs tm) (embed ty) in
                                do log 5 $ "Type of " ++ show n' ++ " : " ++ show tyenv
                                   checkExp loc elabmode env tm tyenv expected
             _ => checkName elabmode loc env x expected
    where
      useVars : List (Term vars) -> Term vars -> Term vars
      useVars [] sc = sc
      useVars (a :: as) (Bind n (Pi _ ty) sc) 
           = Bind n (Let a ty) (useVars (map weaken as) sc)
      useVars _ sc = sc -- Can't happen?

  checkImp process top impmode elabmode env nest (IPi loc plicity Nothing ty retTy) expected 
      = do n <- genName "pi"
           checkPi process top impmode elabmode loc env nest plicity n ty retTy expected
  checkImp process top impmode elabmode env nest (IPi loc plicity (Just n) ty retTy) expected 
      = checkPi process top impmode elabmode loc env nest plicity n ty retTy expected
  checkImp process top impmode elabmode env nest (ILam loc plicity n ty scope) expected
      = checkLam process top impmode elabmode loc env nest plicity n ty scope expected
  checkImp process top impmode elabmode env nest (ILet loc n nTy nVal scope) expected 
      = checkLet process top impmode elabmode loc env nest n nTy nVal scope expected
  checkImp {vars} {c} {u} {i} process top impmode elabmode env nest (ILocal loc nested scope) expected 
      = do let defNames = definedInBlock nested
           est <- get EST
           let f = defining est
           let nest' = record { names $= ((map (applyEnv f) defNames) ++) } nest
           traverse (process c u i env nest') (map (updateName nest') nested)
           checkImp process top impmode elabmode env nest' scope expected
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

  checkImp process top impmode elabmode env nest (IApp loc fn arg) expected 
      = do (fntm, fnty) <- check process top impmode elabmode env nest fn Nothing
           gam <- getCtxt
           -- If the function has an implicit binder in its type, add
           -- the implicits here
           (scopeTy, impArgs) <- getImps loc env (nf gam env fnty) []
           gam <- getCtxt
           case scopeTy of
                NBind _ (Pi _ ty) scdone =>
                  do (argtm, argty) <- check process top impmode elabmode env nest arg (Just (quote empty env ty))
                     let sc' = scdone (toClosure False env argtm)
                     gam <- getCtxt
                     checkExp loc elabmode env (App (apply fntm impArgs) argtm)
                                  (quote gam env sc') expected
                _ => 
                  do bn <- genName "aTy"
                     -- invent names for the argument and return types
                     log 5 $ "Inventing arg type for " ++ show (fn, fnty)
                     (expty, scty) <- inventFnType env bn
                     -- Check the argument type against the invented arg type
                     (argtm, argty) <- 
                         check process top impmode elabmode env nest arg (Just expty) -- (Bind bn (Pi Explicit expty) scty))
                     -- Check the type of 'fn' is an actual function type
                     gam <- getCtxt
                     (fnchk, _) <-
                         checkExp loc elabmode env fntm 
                                  (Bind bn (Pi Explicit expty) scty) 
                                  (Just (quote gam env scopeTy))
                     checkExp loc elabmode env (App fnchk argtm)
                                  (Bind bn (Let argtm argty) scty) expected
  checkImp process top impmode elabmode env nest (IPrimVal loc x) expected 
      = do (x', ty) <- infer loc env (RPrimVal x)
           checkExp loc elabmode env x' ty expected
  checkImp process top impmode elabmode env nest (IType loc) exp
      = checkExp loc elabmode env TType TType exp
  checkImp process top impmode InExpr env nest (IBindVar loc str) exp
      = throw (BadImplicit loc str)
  checkImp process top impmode elabmode env nest (IBindVar loc str) Nothing
      = do let n = PV str
           t <- addHole env TType
           let hty = mkConstantApp t env
           est <- get EST
           case lookup n (boundNames est) of
                Nothing =>
                  do tm <- addBoundName n True env hty
                     put EST 
                         (record { boundNames $= ((n, (tm, hty)) ::),
                                   toBind $= ((n, (tm, hty)) ::) } est)
                     pure (tm, hty)
                Just (tm, ty) =>
                     pure (tm, ty)
  checkImp process top impmode elabmode env nest (IBindVar loc str) (Just expected) 
      = do let n = PV str
           est <- get EST
           case lookup n (boundNames est) of
                Nothing =>
                  do tm <- addBoundName n True env expected
                     log 5 $ "Added Bound implicit " ++ show (n, (tm, expected))
                     put EST 
                         (record { boundNames $= ((n, (tm, expected)) ::),
                                   toBind $= ((n, (tm, expected)) :: ) } est)
                     pure (tm, expected)
                Just (tm, ty) =>
                     checkExp loc elabmode env tm ty (Just expected)
  checkImp process top PATTERN InLHS env nest (IMustUnify loc tm) (Just expected)
      = do (wantedTm, wantedTy) <- checkImp process top PATTERN InLHS env nest tm (Just expected)
           n <- addHole env expected
           gam <- getCtxt
           let tm = mkConstantApp n env
           addDot loc env wantedTm tm
--            constr <- convert loc InLHS env (nf gam env wantedTm) (nf gam env tm)
           checkExp loc InLHS env tm wantedTy (Just expected)
  checkImp process top _ elabmode env nest (IMustUnify loc tm) expected
      = throw (GenericMsg loc "Dot pattern not valid here")
  checkImp process top PATTERN InLHS env nest (IAs loc var tm) (Just expected)
      = do let n = PV var
           est <- get EST
           (patTm, patTy) <- checkImp process top PATTERN InLHS env nest tm (Just expected)
           addBoundName n False env expected
           case lookup n (boundNames est) of
                Just (tm, ty) =>
                    throw (GenericMsg loc ("Name " ++ var ++ " already bound"))
                Nothing =>
                    do tm <- addBoundName n False env expected
                       log 5 $ "Added @ pattern name " ++ show (n, (tm, expected))
                       put EST
                           (record { boundNames $= ((n, (tm, expected)) ::),
                                     toBind $= ((n, (tm, expected)) ::) } est)
                       gam <- getCtxt
                       convert loc InLHS env (nf gam env patTm) (nf gam env tm)
                       pure (patTm, expected)
  checkImp process top _ elabmode env nest (IAs loc var tm) expected
      = throw (GenericMsg loc "@-pattern not valid here")
  checkImp process top impmode elabmode env nest (Implicit loc) Nothing
      = do t <- addHole env TType
           let hty = mkConstantApp t env
           n <- addHole env hty
           pure (mkConstantApp n env, hty)
  checkImp process top impmode elabmode env nest (Implicit loc) (Just expected) 
      = do n <- addHole env expected
           pure (mkConstantApp n env, expected)
 
  checkPi : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            {auto e : Ref EST (EState vars)} ->
            {auto i : Ref ImpST (ImpState annot)} ->
            Elaborator annot ->
            (top : Bool) -> -- top level, unbound implicits bound here
            ImplicitMode -> ElabMode ->
            annot -> Env Term vars -> NestedNames vars -> PiInfo -> Name -> 
            (argty : RawImp annot) -> (retty : RawImp annot) ->
            Maybe (Term vars) ->
            Core annot (Term vars, Term vars) 
  checkPi process top impmode elabmode loc env nest info n argty retty expected
      = do (tyv, tyt) <- check process False impmode elabmode env nest argty (Just TType)
           let env' : Env Term (n :: _) = Pi info tyv :: env
           est <- get EST
           let argImps = if top then (reverse $ toBind est) else []
           when top $ clearToBind 
           e' <- weakenedEState 
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} process top impmode elabmode env' (weaken nest') retty (Just TType)
           est <- get {ref=e'} EST
           let scopeImps = reverse $ toBind est
           st' <- strengthenedEState {e=e'} top loc
           put EST st'
           -- Bind implicits which were first used in
           -- the argument type 'tyv'
           -- This is only in 'PI' implicit mode - it's an error to
           -- have implicits at this level in 'PATT' implicit mode
           case (top, impmode) of
                (True, PI _) =>
                   do -- putStrLn $ "Binding implicits " ++ show (dropTmIn argImps)
                      --                                 ++ show (dropTmIn scopeImps)
                      gam <- getCtxt
                      let (scopev', scopet')
                          = bindImplicits impmode gam env'
                                          (dropTmIn scopeImps) scopev scopet
                      let (binder, bindert)
                          = bindImplicits impmode gam env
                                          (dropTmIn argImps)
                                          (Bind n (Pi info tyv) scopev')
                                          TType
                      traverse (\n => implicitBind n) (map fst scopeImps)
                      traverse (\n => implicitBind n) (map fst argImps)
                      checkExp loc elabmode env binder bindert expected
                _ => checkExp loc elabmode env (Bind n (Pi info tyv) scopev)
                                      TType expected

  checkLam : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             (top : Bool) -> -- top level, unbound implicits bound here
             ImplicitMode -> ElabMode ->
             annot -> Env Term vars -> NestedNames vars -> PiInfo -> Name ->
             (ty : RawImp annot) -> (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkLam process top impmode elabmode loc env nest plicity n ty scope (Just (Bind bn (Pi Explicit pty) psc))
      = do (tyv, tyt) <- check process top impmode elabmode env nest ty (Just TType)
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check process {e=e'} top impmode elabmode (Pi plicity pty :: env) 
                                     (weaken nest') scope 
                                     (Just (renameTop n psc))
           st' <- strengthenedEState top loc
           put EST st'
           checkExp loc elabmode env (Bind n (Lam plicity tyv) scopev)
                        (Bind n (Pi plicity tyv) scopet)
                        (Just (Bind bn (Pi plicity pty) psc))
  checkLam process top impmode elabmode loc env nest plicity n ty scope expected
      = do (tyv, tyt) <- check process top impmode elabmode env nest ty (Just TType)
           let env' : Env Term (n :: _) = Pi Explicit tyv :: env
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} process top impmode elabmode env' (weaken nest') scope Nothing
           st' <- strengthenedEState top loc
           put EST st'
           checkExp loc elabmode env (Bind n (Lam plicity tyv) scopev)
                        (Bind n (Pi plicity tyv) scopet)
                        expected
  
  checkLet : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
             {auto e : Ref EST (EState vars)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Elaborator annot ->
             (top : Bool) -> -- top level, unbound implicits bound here
             ImplicitMode -> ElabMode ->
             annot -> Env Term vars -> NestedNames vars ->
             Name -> 
             (ty : RawImp annot) -> 
             (val : RawImp annot) -> 
             (scope : RawImp annot) ->
             Maybe (Term vars) ->
             Core annot (Term vars, Term vars) 
  checkLet process top impmode elabmode loc env nest n ty val scope expected
      = do (tyv, tyt) <- check process top impmode elabmode env nest ty (Just TType)
           (valv, valt) <- check process top impmode elabmode env nest val (Just tyv)
           let env' : Env Term (n :: _) = Let valv tyv :: env
           e' <- weakenedEState
           let nest' = dropName n nest -- if we see 'n' from here, it's the one we just bound
           (scopev, scopet) <- check {e=e'} process top impmode elabmode env' 
                                     (weaken nest') scope (map weaken expected)
           st' <- strengthenedEState top loc
           put EST st'
           checkExp loc elabmode env (Bind n (Let valv tyv) scopev)
                                     (Bind n (Let valv tyv) scopet)
                                     expected
