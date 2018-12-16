module Core.LinearCheck

import Core.Context
import Core.Normalise
import Core.Options
import Core.TT
import Core.UnifyState -- just for log level

import Data.List

%default covering

lookup : Elem x vars -> Env Term vars -> (RigCount, Term vars)
lookup Here (b :: bs) = (multiplicity b, weaken (binderType b))
lookup (There p) (b :: bs) 
    = case lookup p bs of
           (c, ty) => (c, weaken ty)

-- List of variable usages - we'll count the contents of specific variables
-- when discharging binders, to ensure that linear names are only used once
data Usage : List Name -> Type where
     Nil : Usage vars
     (::) : Elem x vars -> Usage vars -> Usage vars

Show (Usage vars) where
  show xs = "[" ++ showAll xs ++ "]"
    where
      showAll : Usage vs -> String
      showAll [] = ""
      showAll {vs = v :: _} [el] = show v
      showAll {vs = v :: _} (x :: xs) = show v ++ ", " ++ show xs

Weaken Usage where
  weaken [] = []
  weaken (x :: xs) = There x :: weaken xs

doneScope : Usage (n :: vars) -> Usage vars
doneScope [] = []
doneScope (Here :: xs) = doneScope xs
doneScope (There p :: xs) = p :: doneScope xs

(++) : Usage ns -> Usage ns -> Usage ns
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

count : Elem x ns -> Usage ns -> Nat
count p [] = 0
count p (q :: xs) = if sameVar p q then 1 + count p xs else count p xs

-- If there are holes in the given term, update the hole's type to reflect
-- whether the given variable was used (in a Rig1 position) elsewhere.
-- If it *was* used elsewhere, the hole's type should have it at a rig
-- count of zero, otherwise its rig count should be left alone.
-- That is: the 'useInHole' argument reflects whether the given variable
-- should be treated as Rig1.

-- If there's more than one hole, treat the holes independently. That is,
-- the hole is to help the programmer, so set the type such that the variable
-- is available for each hole.
-- While this isn't strictly right for QTT's notion of usage, it means that
-- the usage information shown for each hole is more useful for interactive
-- editing.

-- Returns 'False' if no hole encountered (so no need to change usage data
-- for the rest of the definition)
mutual
  updateHoleUsageArgs : {auto c : Ref Ctxt Defs} ->
                        {auto u : Ref UST (UState annot)} ->
                        (useInHole : Bool) ->
                        Elem x vars -> List (Term vars) -> Core annot Bool 
  updateHoleUsageArgs useInHole var [] = pure False
  updateHoleUsageArgs useInHole var (a :: as)
      = do h <- updateHoleUsage useInHole var a
           h' <- updateHoleUsageArgs useInHole var as
           pure (h || h')

  updateHoleType : {auto c : Ref Ctxt Defs} ->
                   {auto u : Ref UST (UState annot)} ->
                   (useInHole : Bool) ->
                   Elem x vars -> Nat -> Term vs -> List (Term vars) ->
                   Core annot (Term vs)
  updateHoleType useInHole var (S k) (Bind nm (Pi c e ty) sc) (Local r v :: as)
      -- if the argument to the hole type is the variable of interest,
      -- and the variable should be used in the hole, set it to Rig1,
      -- otherwise set it to Rig0
      = if sameVar var v
           then do scty <- updateHoleType False var k sc as
                   let c' = if useInHole then c else Rig0
                   pure (Bind nm (Pi c' e ty) scty)
           else do scty <- updateHoleType useInHole var k sc as
                   pure (Bind nm (Pi c e ty) scty)
  updateHoleType useInHole var (S k) (Bind nm (Pi c e ty) sc) (a :: as)
      = do updateHoleUsage False var a
           scty <- updateHoleType useInHole var k sc as
           pure (Bind nm (Pi c e ty) scty)
  updateHoleType useInHole var _ ty as 
      = do updateHoleUsageArgs False var as
           pure ty

  updateHoleUsage : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST (UState annot)} ->
                    (useInHole : Bool) ->
                    Elem x vars -> Term vars -> Core annot Bool 
  updateHoleUsage useInHole var (Bind n (Let c val ty) sc)
        = do h <- updateHoleUsage useInHole var val
             h' <- updateHoleUsage useInHole (There var) sc
             pure (h || h')
  updateHoleUsage useInHole var (Bind n b sc)
        = updateHoleUsage useInHole (There var) sc
  updateHoleUsage useInHole var tm with (unapply tm)
    updateHoleUsage useInHole var (apply (Ref nt fn) args) | ArgsList 
        = do gam <- getCtxt
             case lookupDefTyExact fn gam of
                  Just (Hole locs pvar _, ty)
                    => do ty' <- updateHoleType useInHole var locs ty args
                          log 5 $ "Updated hole type " ++ show fn ++ " : " ++ show ty'
                          updateTy fn ty'
                          pure True
                  _ => updateHoleUsageArgs useInHole var args
    updateHoleUsage useInHole var (apply f []) | ArgsList 
        = pure False
    updateHoleUsage useInHole var (apply f args) | ArgsList 
        = updateHoleUsageArgs useInHole var (f :: args)

-- Linearity checking of an already checked term. This serves two purposes:
--  + Checking correct usage of linear bindings
--  + updating hole types to reflect usage counts correctly
-- Returns term, (head-)normalised type, a list of used variables and
-- whether the term is an application to a borrowed name
mutual
  lcheck : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST (UState annot)} ->
           annot -> RigCount -> (erase : Bool) -> Env Term vars -> Term vars -> 
           Core annot (Term vars, Lazy (NF vars), Usage vars, Maybe (Term vars))
  lcheck loc rig erase env tm
      = do (tm, ty, usage, borrow) <- lcheck' loc rig erase env tm
           maybe (pure ()) 
              (\t => case ty of
                          NTCon _ _ _ _ => pure ()
                          NPrimVal _ => pure ()
                          NType => pure ()
                          _ => throw (BorrowPartial loc env tm t)) borrow
           pure (tm, ty, usage, borrow)

  lcheck' : {auto c : Ref Ctxt Defs} ->
            {auto u : Ref UST (UState annot)} ->
            annot -> RigCount -> (erase : Bool) -> Env Term vars -> Term vars -> 
            Core annot (Term vars, Lazy (NF vars), Usage vars, Maybe (Term vars))
  lcheck' {vars} loc rig erase env (Local {x} r v) 
      = let (rigb, ty) = lookup v env in
            do gam <- get Ctxt
               rigSafe rigb rig
               pure (Local r v, nf gam env ty, used rig, Nothing)
    where
      rigSafe : RigCount -> RigCount -> Core annot ()
      rigSafe (Rig1 b) RigW = throw (LinearMisuse loc x (Rig1 b) RigW)
      rigSafe Rig0 RigW = throw (LinearMisuse loc x Rig0 RigW)
      rigSafe Rig0 (Rig1 b) = throw (LinearMisuse loc x Rig0 (Rig1 b))
      rigSafe _ _ = pure ()

      -- count the usage if we're in a linear context. If not, the usage doesn't
      -- matter
      used : RigCount -> Usage vars
      used (Rig1 False) = [v] -- only if not borrowed
      used _ = []

  lcheck' loc rig erase env (Ref nt fn)
      = do gam <- get Ctxt
           case lookupDefTyExact fn (gamma gam) of
                Nothing => throw (InternalError ("Linearity checking failed on " ++ show fn))
                -- Don't count variable usage in holes, so as far as linearity
                -- checking is concerned, update the type so that the binders
                -- are in Rig0
                Just (Hole locs _ _, ty) => 
                     pure (Ref nt fn, nf gam env (embed (unusedHoleArgs locs ty)), 
                           [], Nothing)
                Just (def, ty) => 
                     pure (Ref nt fn, nf gam env (embed ty), [], Nothing)
    where
      unusedHoleArgs : Nat -> Term vars -> Term vars
      unusedHoleArgs (S k) (Bind n (Pi _ e ty) sc)
          = Bind n (Pi Rig0 e ty) (unusedHoleArgs k sc)
      unusedHoleArgs _ ty = ty

  lcheck' {vars} loc rig_in erase env (Bind nm b sc)
      = do (b', bt, usedb) <- lcheckBinder loc rig erase env b
           (sc', sct, usedsc, _) <- lcheck loc rig erase (b' :: env) sc
           gam <- get Ctxt

           when (not (isExtension Borrowing gam)) $
                case multiplicity b of
                     Rig1 True => throw (GenericMsg loc "Borrowing extension not enabled")
                     _ => pure ()

           let used_in = count Here usedsc
           log 10 (show rig ++ " " ++ show nm ++ ": " ++ show used_in)
           holeFound <- if isLinear (multiplicity b)
                           then updateHoleUsage (used_in == 0) Here sc'
                           else pure False

           -- if there's a hole, assume it will contain the missing usage
           -- if there is none already
           let used = case rigMult (multiplicity b) rig of
                           Rig1 False => if holeFound && used_in == 0 
                                            then 1 
                                            else used_in
                           _ => used_in

           checkUsageOK used (rigMult (multiplicity b) rig)
           gam <- get Ctxt
           let bt = discharge gam env nm b' bt sc' sct (usedb ++ doneScope usedsc)
           borrowOK gam b (fst bt)
           pure bt
    where
      rig : RigCount
      rig = case b of
                 Pi _ _ _ => Rig0
                 _ => rig_in

      concreteRet : NF vars -> Bool
      concreteRet (NBind _ _ sc) 
          = concreteRet (sc (toClosure defaultOpts env Erased))
      concreteRet (NTCon _ _ _ _) = True
      concreteRet (NPrimVal _) = True
      concreteRet _ = False

      borrowOK : Defs -> Binder (Term vars) -> Term vars -> Core annot ()
      borrowOK gam (Pi (Rig1 True) _ _) ty
          = when (not (concreteRet (nf gam env ty))) $
                 throw (BorrowPartialType loc env ty)
      borrowOK _ _ _ = pure ()

      checkUsageOK : Nat -> RigCount -> Core annot ()
      checkUsageOK used Rig0 = pure ()
      checkUsageOK used RigW = pure ()
      checkUsageOK used (Rig1 False)
          = if used == 1 
               then pure ()
               else throw (LinearUsed loc used nm)
      checkUsageOK used (Rig1 True)
          = if used == 0 
               then pure ()
               else throw (LinearMisuse loc nm (Rig1 True) (Rig1 False))

  lcheck' loc rig erase env (App f a)
      = do (f', fty, fused, fborrow) <- lcheck' loc rig erase env f
           -- ^ lcheck' because we don't check that the function is fully
           -- applied if there's borrowing here
           gam <- get Ctxt
           case fty of
                NBind _ (Pi rigf _ ty) scdone =>
                     -- if the argument is borrowed, it's okay to use it in
                     -- unrestricted context, because we'll be out of the
                     -- application without spending it
                   do let checkRig = case (rigf, rig) of
                                          (Rig1 True, Rig0) => Rig0
                                          (Rig1 True, _) => Rig1 True
                                          _ => rigMult rigf rig
                      (a', aty, aused, _) <- lcheck loc checkRig erase env a
                      let sc' = scdone (toClosure defaultOpts env a')
                      let aerased = if erase && rigf == Rig0 then Erased else a'
                      -- Possibly remove this check, or make it a compiler
                      -- flag? It is a useful double check on the result of
                      -- elaboration, but there are pathological cases where
                      -- it makes the check very slow (id id id id ... id id etc
                      -- for example) and there may be similar realistic cases.
                      -- If elaboration is correct, this should never fail!
                      when (not (convert gam env aty ty)) $
                         throw (CantConvert loc env (quote (noGam gam) env ty) 
                                                    (quote (noGam gam) env aty))
                      pure (App f' aerased, sc', fused ++ aused, fborrow <+> isBorrow rigf a')
                _ => throw (InternalError ("Linearity checking failed on " ++ show f' ++ 
                              " (" ++ show (quote gam env fty) ++ " not a function type)"))
    where
      isBorrow : RigCount -> Term vars -> Maybe (Term vars)
      isBorrow (Rig1 True) t = Just t
      isBorrow _ _ = Nothing

  lcheck' loc rig erase env (PrimVal x) = pure (PrimVal x, NErased, [], Nothing)
  lcheck' loc rig erase env Erased = pure (Erased, NErased, [], Nothing)
  lcheck' loc rig erase env TType = pure (TType, NType, [], Nothing)

  lcheckBinder : {auto c : Ref Ctxt Defs} ->
                 {auto u : Ref UST (UState annot)} ->
                 annot -> RigCount -> (erase : Bool) -> Env Term vars -> 
                 Binder (Term vars) -> 
                 Core annot (Binder (Term vars), Lazy (NF vars), Usage vars)
  lcheckBinder loc rig erase env (Lam c x ty)
      = do (tyv, tyt, _, _) <- lcheck loc Rig0 erase env ty
           pure (Lam c x tyv, tyt, [])
  lcheckBinder loc rig erase env (Let rigc val ty)
      = do (tyv, tyt, _, _) <- lcheck loc Rig0 erase env ty
           (valv, valt, vs, _) <- lcheck loc (rigMult rig rigc) erase env val
           pure (Let rigc valv tyv, tyt, vs)
  lcheckBinder loc rig erase env (Pi c x ty)
      = do (tyv, tyt, _, _) <- lcheck loc Rig0 erase env ty
           pure (Pi c x tyv, tyt, [])
  lcheckBinder loc rig erase env (PVar c ty)
      = do (tyv, tyt, _, _) <- lcheck loc Rig0 erase env ty
           pure (PVar c tyv, tyt, [])
  lcheckBinder loc rig erase env (PLet rigc val ty)
      = do (tyv, tyt, _, _) <- lcheck loc Rig0 erase env ty
           (valv, valt, vs, _) <- lcheck loc (rigMult rig rigc) erase env val
           pure (PLet rigc valv tyv, tyt, vs)
  lcheckBinder loc rig erase env (PVTy c ty)
      = do (tyv, tyt, _, _) <- lcheck loc Rig0 erase env ty
           pure (PVTy c tyv, tyt, [])
  
  discharge : Defs -> Env Term vars ->
              (nm : Name) -> Binder (Term vars) -> Lazy (NF vars) ->
              Term (nm :: vars) -> Lazy (NF (nm :: vars)) -> Usage vars ->
              (Term vars, Lazy (NF vars), Usage vars, Maybe (Term vars))
  discharge gam env nm (Lam c x ty) bindty scope scopety used
       = let sctytm = quote (noGam gam) (Pi c x ty :: env) scopety
             bty = nf gam env (Bind nm (Pi c x ty) sctytm) in
             (Bind nm (Lam c x ty) scope, bty, used, Nothing)
  discharge gam env nm (Let c val ty) bindty scope scopety used
       = let sctytm = quote (noGam gam) (Let c val ty :: env) scopety
             bty = nf gam env (Bind nm (Let c val ty) sctytm) in
             (Bind nm (Let c val ty) scope, bty, used, Nothing)
  discharge gam env nm (Pi c x ty) bindty scope scopety used
       = (Bind nm (Pi c x ty) scope, bindty, used, Nothing)
  discharge gam env nm (PVar c ty) bindty scope scopety used
       = let sctytm = quote (noGam gam) (PVTy c ty :: env) scopety
             bty = nf gam env (Bind nm (PVTy c ty) sctytm) in
             (Bind nm (PVar c ty) scope, bty, used, Nothing)
  discharge gam env nm (PLet c val ty) bindty scope scopety used
       = let sctytm = quote (noGam gam) (PLet c val ty :: env) scopety
             bty = nf gam env (Bind nm (PLet c val ty) sctytm) in
             (Bind nm (PLet c val ty) scope, bty, used, Nothing)
  discharge gam env nm (PVTy c ty) bindty scope scopety used
       = (Bind nm (PVTy c ty) scope, bindty, used, Nothing)

checkEnvUsage : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState annot)} ->
                annot -> RigCount -> 
                Env Term vars -> Usage (done ++ vars) -> Term (done ++ vars) -> Core annot ()
checkEnvUsage loc rig [] usage tm = pure ()
checkEnvUsage loc rig {done} {vars = nm :: xs} (b :: env) usage tm
    = do let pos = localPrf {later = done}
         let used_in = count pos usage

         holeFound <- if isLinear (multiplicity b)
                         then updateHoleUsage (used_in == 0) pos tm
                         else pure False
         let used = case rigMult (multiplicity b) rig of
                         Rig1 False => if holeFound && used_in == 0 
                                          then 1 
                                          else used_in
                         _ => used_in
         checkUsageOK used (rigMult (multiplicity b) rig)
         checkEnvUsage {done = done ++ [nm]} loc rig env 
               (rewrite sym (appendAssociative done [nm] xs) in usage)
               (rewrite sym (appendAssociative done [nm] xs) in tm)
  where
    checkUsageOK : Nat -> RigCount -> Core annot ()
    checkUsageOK used Rig0 = pure ()
    checkUsageOK used RigW = pure ()
    checkUsageOK used (Rig1 False)
        = if used == 1 
             then pure ()
             else throw (LinearUsed loc used nm)
    checkUsageOK used (Rig1 True)
        = if used == 0 
             then pure ()
             else throw (LinearMisuse loc nm (Rig1 True) (Rig1 False))

-- Linearity check an elaborated term. If 'erase' is set, erase anything that's in
-- a Rig0 argument position (we can't do this until typechecking is complete, though,
-- since it might be used for unification/reasoning elsewhere, so we only do this for
-- definitions ready for compilation).
export
linearCheck : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              annot -> RigCount -> (erase : Bool) ->
              Env Term vars -> Term vars -> 
              Core annot (Term vars)
linearCheck loc rig erase env tm
    = do log 5 $ "Linearity check on " ++ show (bindEnv env tm)
         (tm', _, used, _) <- lcheck loc rig erase env tm
         when (not erase) $ checkEnvUsage {done = []} loc rig env used tm'
         pure tm'

