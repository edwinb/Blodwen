module TTImp.ProcessDef

import Core.TT
import Core.Unify
import Core.Context
import Core.CaseBuilder
import Core.Normalise
import Core.Reflect

import TTImp.Elab
import TTImp.TTImp

import Data.List
import Control.Catchable

mutual
  mismatchNF : Defs -> NF vars -> NF vars -> Bool
  mismatchNF gam (NTCon _ xt _ xargs) (NTCon _ yt _ yargs) 
      = if xt /= yt 
           then True
           else any (mismatch gam) (zip xargs yargs) 
  mismatchNF gam (NDCon _ xt _ xargs) (NDCon _ yt _ yargs) 
      = if xt /= yt
           then True
           else any (mismatch gam) (zip xargs yargs) 
  mismatchNF gam (NPrimVal xc) (NPrimVal yc) = xc /= yc
  mismatchNF _ _ _ = False

  mismatch : Defs -> (Closure vars, Closure vars) -> Bool
  mismatch gam (x, y) = mismatchNF gam (evalClosure gam x) (evalClosure gam y)

-- Find names which are applied to a function in a Rig1/Rig0 position,
-- so that we know how they should be bound on the right hand side of the
-- pattern.
-- 'bound' counts the number of variables locally bound; these are the
-- only ones we're checking linearity of (we may be shadowing names if this
-- is a local definition, so we need to leave the earlier ones alone)
findLinear : Defs -> Nat -> RigCount -> Term vars -> List (Name, RigCount)
findLinear gam bound rig (Bind n b sc) = findLinear gam (S bound) rig sc
findLinear gam bound rig tm with (unapply tm)
  findLinear gam bound rig (apply (Ref _ n) []) | ArgsList = []
  findLinear gam bound rig (apply (Ref _ n) args) | ArgsList 
      = case lookupTyExact n (gamma gam) of
             Nothing => []
             Just nty => findLinArg (nf gam [] nty) args
    where
      boundHere : Nat -> Elem x xs -> Bool
      boundHere Z p = False
      boundHere (S k) Here = True
      boundHere (S k) (There p) = boundHere k p

      findLinArg : NF [] -> List (Term vars) -> List (Name, RigCount)
      findLinArg (NBind x (Pi c _ _) sc) (Local {x=a} _ prf :: as) 
          = if boundHere bound prf
               then (a, rigMult c rig) :: 
                    findLinArg (sc (toClosure defaultOpts [] (Ref Bound x))) as
               else findLinArg (sc (toClosure defaultOpts [] (Ref Bound x))) as
      findLinArg (NBind x (Pi c _ _) sc) (a :: as) 
          = findLinear gam bound (rigMult c rig) a ++
                findLinArg (sc (toClosure defaultOpts [] (Ref Bound x))) as
      findLinArg ty (a :: as) = findLinear gam bound rig a ++ findLinArg ty as
      findLinArg _ [] = []
  findLinear gam bound rig (apply f args) | ArgsList = []

setLinear : List (Name, RigCount) -> Term vars -> Term vars
setLinear vs (Bind x (PVar c ty) sc)
    = case lookup x vs of
           Just c' => Bind x (PVar c' ty) (setLinear vs sc)
           _ => Bind x (PVar c ty) (setLinear vs sc)
setLinear vs (Bind x (PVTy c ty) sc)
    = case lookup x vs of
           Just c' => Bind x (PVTy c' ty) (setLinear vs sc)
           _ => Bind x (PVTy c ty) (setLinear vs sc)
setLinear vs tm = tm

-- Combining multiplicities on LHS:
-- Rig1 + Rig1/W not valid, since it means we have repeated use of name
-- Rig0 + RigW = RigW
-- Rig0 + Rig1 = Rig1
combineLinear : annot -> List (Name, RigCount) ->
                Core annot (List (Name, RigCount))
combineLinear loc [] = pure []
combineLinear loc ((n, count) :: cs)
    = case lookupAll n cs of
           [] => pure $ (n, count) :: !(combineLinear loc cs)
           counts => do count' <- combineAll count counts
                        pure $ (n, count') :: 
                               !(combineLinear loc (filter notN cs))
  where
    notN : (Name, RigCount) -> Bool
    notN (n', _) = n /= n'

    lookupAll : Name -> List (Name, RigCount) -> List RigCount
    lookupAll n [] = []
    lookupAll n ((n', c) :: cs) 
       = if n == n' then c :: lookupAll n cs else lookupAll n cs

    combine : RigCount -> RigCount -> Core annot RigCount
    combine Rig1 Rig1 = throw (LinearUsed loc 2 n)
    combine Rig1 RigW = throw (LinearUsed loc 2 n)
    combine RigW Rig1 = throw (LinearUsed loc 2 n)
    combine RigW RigW = pure RigW
    combine Rig0 c = pure c
    combine c Rig0 = pure c

    combineAll : RigCount -> List RigCount -> Core annot RigCount
    combineAll c [] = pure c
    combineAll c (c' :: cs)
        = do newc <- combine c c'
             combineAll newc cs

-- If the terms have the same type constructor at the head, and one of
-- the argument positions has different constructors at its head, then this
-- is an impossible case, so return True
impossibleOK : Defs -> NF vars -> NF vars -> Bool
impossibleOK gam (NTCon xn xt xa xargs) (NTCon tn yt ya yargs)
    = any (mismatch gam) (zip xargs yargs)
impossibleOK _ _ _ = False

checkClause : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              Reflect annot =>
              Elaborator annot ->
              Name ->
              Env Term vars -> NestedNames vars -> ImpClause annot ->
              Core annot (Maybe (Clause, Clause)) -- Compile time vs run time clauses
                     -- (the run time version has had 0-multiplicities erased)
checkClause elab defining env nest (ImpossibleClause loc lhs_raw)
    = handleClause
         (do lhs_raw <- lhsInCurrentNS nest lhs_raw
             (lhs_in, _, lhsty_in) <- inferTerm elab defining env nest PATTERN InLHS lhs_raw
             gam <- get Ctxt
             let lhs = normaliseHoles gam env lhs_in
             let lhsty = normaliseHoles gam env lhsty_in
             throw (ValidCase loc env (Left lhs)))
         (\err => case err of
                       ValidCase _ _ _ => throw err
                       WhenUnifying _ env l r err
                           => do gam <- get Ctxt
                                 if impossibleOK gam (nf gam env l) (nf gam env r)
                                    then pure Nothing
                                    else throw (ValidCase loc env (Right err))
                       _ => throw (ValidCase loc env (Right err)))
checkClause {vars} elab defining env nest (PatClause loc lhs_raw rhs_raw)
    = do gam <- get Ctxt
         lhs_raw_in <- lhsInCurrentNS nest lhs_raw
         let lhs_raw = implicitsAs gam vars lhs_raw_in
         log 5 ("Checking LHS: " ++ show lhs_raw)
         (lhs_in, _, lhsty_in) <- wrapError (InLHS loc defining) $
              inferTerm elab defining env nest PATTERN InLHS lhs_raw
         -- Check there's no holes or constraints in the left hand side
         -- we've just checked - they must be resolved now (that's what
         -- True means)
         gam <- get Ctxt
         wrapError (InLHS loc defining) $ checkUserHoles True
         -- Normalise the LHS to get any functions or let bindings evaluated
         -- (this might be allowed, e.g. for 'fromInteger')
         let lhs = normalise gam env lhs_in
         let lhsty = normaliseHoles gam env lhsty_in
         let linvars_in = findLinear gam 0 Rig1 lhs
         log 5 $ "Linearity of names in " ++ show defining ++ ": " ++ 
                 show linvars_in

         linvars <- combineLinear loc linvars_in
         let lhs' = setLinear linvars lhs
         let lhsty' = setLinear linvars lhsty

         -- Extend the environment with the names bound on the LHS, but also
         -- remember the outer environment.  Everything there is treated as
         -- parameters, and this is important when making types for case
         -- expressions (we don't want to abstract over the outer environment
         -- again)
         (vs ** (prf, env', nest', lhspat, reqty)) <- extend env SubRefl nest lhs' lhsty'
         log 3 ("LHS: " ++ show lhs' ++ " : " ++ show reqty)
         log 5 ("Checking RHS: " ++ show rhs_raw)
         log 10 ("Old env: " ++ show env)
         log 10 ("New env: " ++ show env')
         (rhs, rhs_erased) <- wrapError (InRHS loc defining) $
                checkTerm elab defining env' env prf nest' NONE InExpr rhs_raw reqty
         log 5 ("Checked and erased RHS: " ++ show rhs_erased)

         -- only need to check body for visibility if name is
         -- public
         let vis = case lookupGlobalExact defining (gamma gam) of
                        Just d => visibility d
                        Nothing => Public

         when (vis == Public) $ do
           checkNameVisibility loc defining vis lhs
           checkNameVisibility loc defining vis rhs


         log 3 ("Clause: " ++ show lhspat ++ " = " ++ show rhs)
         pure (Just (MkClause env' lhspat rhs, MkClause env' lhspat rhs_erased))
  where
    extend : Env Term extvs -> SubVars vs extvs ->
             NestedNames extvs -> 
             Term extvs -> Term extvs ->
             Core annot (vars' ** (SubVars vs vars',
                                   Env Term vars', NestedNames vars', 
                                   Term vars', Term vars'))
    extend env p nest (Bind n (PVar c tmsc) sc) (Bind n' (PVTy _ _) tysc) with (nameEq n n')
      extend env p nest (Bind n (PVar c tmsc) sc) (Bind n' (PVTy _ _) tysc) | Nothing 
            = throw (InternalError "Names don't match in pattern type")
      extend env p nest (Bind n (PVar c tmsc) sc) (Bind n (PVTy _ _) tysc) | (Just Refl) 
            = extend (PVar c tmsc :: env) (DropCons p) (weaken nest) sc tysc
    extend env p nest (Bind n (PLet c tmv tmt) sc) (Bind n' (PLet _ _ _) tysc) with (nameEq n n')
      extend env p nest (Bind n (PLet c tmv tmt) sc) (Bind n' (PLet _ _ _) tysc) | Nothing 
            = throw (InternalError "Names don't match in pattern type")
      -- PLet on the left becomes Let on the right, to give it computational force
      extend env p nest (Bind n (PLet c tmv tmt) sc) (Bind n (PLet _ _ _) tysc) | (Just Refl) 
            = extend (Let c tmv tmt :: env) (DropCons p) (weaken nest) sc tysc
    extend env p nest tm ty = pure (_ ** (p, env, nest, tm, ty))

nameListEq : (xs : List Name) -> (ys : List Name) -> Maybe (xs = ys)
nameListEq [] [] = Just Refl
nameListEq (x :: xs) (y :: ys) with (nameEq x y)
  nameListEq (x :: xs) (x :: ys) | (Just Refl) with (nameListEq xs ys)
    nameListEq (x :: xs) (x :: xs) | (Just Refl) | Just Refl= Just Refl
    nameListEq (x :: xs) (x :: ys) | (Just Refl) | Nothing = Nothing
  nameListEq (x :: xs) (y :: ys) | Nothing = Nothing
nameListEq _ _ = Nothing

export
processDef : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             Reflect annot =>
             Elaborator annot ->
             Env Term vars -> NestedNames vars -> annot ->
             Name -> List (ImpClause annot) -> 
             Core annot ()
processDef elab env nest loc n_in cs_raw
    = do gam <- getCtxt
         n <- inCurrentNS n_in
         case lookupDefTyExact n gam of
              Nothing => throw (NoDeclaration loc n)
              Just (None, ty) =>
                do cs <- traverse (checkClause elab n env nest) cs_raw
                   (cargs ** tree_comp) <- getPMDef loc n ty (map fst (mapMaybe id cs))
                   (rargs ** tree_rt) <- getPMDef loc n ty (map snd (mapMaybe id cs))
                   
                   let Just Refl = nameListEq cargs rargs
                           | Nothing => throw (InternalError "WAT")
                   addFnDef loc n tree_comp tree_rt
                   
                   addToSave n
                   gam <- getCtxt
                   log 3 $
                      case lookupDefExact n gam of
                           Just (PMDef _ args tc tr) =>
                              "Case tree for " ++ show n ++ "\n\t" ++
                              show args ++ " " ++ show tc ++ "\n" ++
                              "Run time tree\n" ++
                              show args ++ " " ++ show tr
                           _ => "No case tree for " ++ show n
              Just (_, ty) => throw (AlreadyDefined loc n)
