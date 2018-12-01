module TTImp.ProcessDef

import Core.TT
import Core.Unify
import Core.Context
import Core.CaseBuilder
import Core.LinearCheck
import Core.Metadata
import Core.Normalise
import Core.Reflect

import TTImp.Elab
import TTImp.TTImp
import TTImp.Utils

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

-- If the terms have the same type constructor at the head, and one of
-- the argument positions has different constructors at its head, then this
-- is an impossible case, so return True
export
impossibleOK : Defs -> NF vars -> NF vars -> Bool
impossibleOK gam (NTCon xn xt xa xargs) (NTCon tn yt ya yargs)
    = any (mismatch gam) (zip xargs yargs)
impossibleOK _ _ _ = False

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

-- Return an extended environment. The 'SubVars' proof contains a proof that
-- refers to the *inner* environment, so all the outer things are marked as
-- 'DropCons'
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

bindNotReq : Int -> Env Term vs -> (sub : SubVars pre vs) -> 
             Term vs -> Term pre
bindNotReq i [] SubRefl tm = embed tm
bindNotReq i (b :: env) SubRefl tm 
   = let tmptm = subst (Ref Bound (MN "arg" i)) tm 
         btm = bindNotReq (1 + i) env SubRefl tmptm in
         refToLocal (Just (multiplicity b)) (MN "arg" i) _ btm
bindNotReq i (b :: env) (KeepCons p) tm 
   = let tmptm = subst (Ref Bound (MN "arg" i)) tm 
         btm = bindNotReq (1 + i) env p tmptm in
         refToLocal (Just (multiplicity b)) (MN "arg" i) _ btm
bindNotReq i (b :: env) (DropCons p) tm 
   = bindNotReq i env p 
       (Bind _ (Pi (multiplicity b) Explicit (binderType b)) tm)

bindReq : Env Term vs -> (sub : SubVars pre vs) -> 
          Term pre -> Maybe ClosedTerm -- (notreqInSub vs sub)
bindReq env SubRefl tm = pure (bindEnv env tm)
bindReq (b :: env) (KeepCons p) tm 
   = do b' <- shrinkBinder b p
        bindReq env p 
           (Bind _ (Pi (multiplicity b) Explicit (binderType b')) tm)
bindReq (b :: env) (DropCons p) tm = bindReq env p tm

getReq : (vs : List Name) -> SubVars pre vs -> List Name
getReq vs SubRefl = vs
getReq _ (DropCons p) = getReq _ p
getReq (v :: vs) (KeepCons p) = v :: getReq _ p

getNotReq : (vs : List Name) -> SubVars pre vs -> List Name
getNotReq vs SubRefl = []
getNotReq (v :: vs) (DropCons p) = v :: getNotReq _ p
getNotReq _ (KeepCons p) = getNotReq _ p

checkLHS : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST (UState annot)} ->
           {auto i : Ref ImpST (ImpState annot)} ->
           {auto m : Ref Meta (Metadata annot)} ->
           Reflect annot =>
           annot -> Elaborator annot ->
           (incase : Bool) -> (mult : RigCount) -> (hashit : Bool) ->
           Name ->
           Env Term vars -> NestedNames vars -> RawImp annot ->
           Core annot (vars' ** (SubVars vars vars',
                                 Env Term vars', NestedNames vars', 
                                 Term vars', Term vars'))
checkLHS {vars} loc elab incase mult hashit defining env nest lhs_raw
    = do gam <- get Ctxt
         lhs_raw_in <- lhsInCurrentNS nest lhs_raw
         let lhs_raw = implicitsAs gam vars lhs_raw_in
         log 5 ("Checking LHS: " ++ show lhs_raw)
         (lhs_in, _, lhsty_in) <- wrapError (InLHS loc defining) $
              inferTerm elab incase defining env nest
                        PATTERN (InLHS mult) lhs_raw
         -- Check there's no holes or constraints in the left hand side
         -- we've just checked - they must be resolved now (that's what
         -- True means)
         gam <- get Ctxt
         when (not incase) $
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
         log 3 ("LHS: " ++ show lhs' ++ " : " ++ show lhsty')
         setHoleLHS (bindEnv env lhs')

         -- Extend the environment with the names bound on the LHS, but also
         -- remember the outer environment.  Everything there is treated as
         -- parameters, and this is important when making types for case
         -- expressions (we don't want to abstract over the outer environment
         -- again)
         extend env SubRefl nest lhs' lhsty'

export -- to allow program search to use it to check candidate clauses
checkClause : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              {auto m : Ref Meta (Metadata annot)} ->
              Reflect annot =>
              Elaborator annot ->
              (incase : Bool) -> (mult : RigCount) -> (hashit : Bool) ->
              Name ->
              Env Term vars -> NestedNames vars -> ImpClause annot ->
              Core annot (Maybe (Clause, Clause)) -- Compile time vs run time clauses
                     -- (the run time version has had 0-multiplicities erased)
checkClause elab incase mult hashit defining env nest (ImpossibleClause loc lhs_raw)
    = handleClause
         (do lhs_raw <- lhsInCurrentNS nest lhs_raw
             (lhs_in, _, lhsty_in) <- inferTerm elab incase defining env nest
                                                PATTERN (InLHS mult) lhs_raw
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
checkClause {vars} elab incase mult hashit defining env nest (PatClause loc lhs_raw rhs_raw)
    = do (vs ** (prf, env', nest', lhspat, reqty)) <- 
            checkLHS loc elab incase mult hashit defining env nest lhs_raw
         gam <- get Ctxt

         log 5 ("Checking RHS: " ++ show rhs_raw)
         log 10 ("Old env: " ++ show env)
         log 10 ("New env: " ++ show env')

         let mode
               = case mult of
                      Rig0 => InType -- treat as used in type only
                      _ => InExpr
         (rhs, rhs_erased) <- wrapError (InRHS loc defining) $
                checkTerm elab incase defining env' env prf nest' NONE mode rhs_raw reqty
         clearHoleLHS
         log 5 ("Checked and erased RHS: " ++ show rhs_erased)

         -- only need to check body for visibility if name is
         -- public
         let vis = case lookupGlobalExact defining (gamma gam) of
                        Just d => visibility d
                        Nothing => Public

         when (vis == Public) $ do
           checkNameVisibility loc defining vis lhspat
           checkNameVisibility loc defining vis rhs

         addLHS (getAnnot lhs_raw) (length env) env' lhspat
         log 3 ("Clause: " ++ show lhspat ++ " = " ++ show rhs)
         when hashit $ 
           do addHash lhspat
              addHash rhs
         pure (Just (MkClause env' lhspat rhs, MkClause env' lhspat rhs_erased))
checkClause {c} {u} {i} {m} {vars} elab incase mult hashit defining env nest (WithClause loc lhs_raw_src wval_raw cs)
    = do (vs ** (prf, env', nest', lhspat, reqty)) <- 
            checkLHS loc elab incase mult hashit defining env nest lhs_raw_src
         gam <- get Ctxt

         log 5 ("Checking with value: " ++ show wval_raw)
         log 10 ("Old env: " ++ show env)
         log 10 ("New env: " ++ show env')

         let mode
               = case mult of
                      Rig0 => InType -- treat as used in type only
                      _ => InExpr

         (wval, wval_erased, wvalTy) <- wrapError (InRHS loc defining) $
                inferTermEnv elab incase defining env' env prf nest' NONE mode wval_raw
         clearHoleLHS

         let (wevars ** withSub) = keepOldEnv prf (snd (findSubEnv env' wval))

         let Just wval = shrinkTerm wval withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #1")
         let Just wvalTy = shrinkTerm wvalTy withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #2")
         let Just wvalEnv = shrinkEnv env' withSub
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #3")
         log 5 ("With value: " ++ show wval ++ " : " ++ show wvalTy)
         log 5 ("Uses env: " ++ show wevars)
         log 5 ("Required type: " ++ show reqty)

         -- TODO: Also abstract over 'wval' in the scope of bNotReq in order
         -- to get the 'magic with' behaviour
         let wargn = MN "warg" 0
         let scenv = Pi RigW Explicit wvalTy :: wvalEnv

         let wtyScope = replace gam scenv (nf gam scenv (weaken wval))
                            (Local (Just RigW) Here)
                            (nf gam scenv 
                                (weaken (bindNotReq 0 env' withSub reqty)))
         let bNotReq = Bind wargn (Pi RigW Explicit wvalTy) wtyScope
         log 10 ("Bound unrequired vars: " ++ show bNotReq)

         let Just wtype = bindReq env' withSub bNotReq
             | Nothing => throw (InternalError "Impossible happened: With abstraction failure #4")

         -- list of argument names - 'Just' means we need to match the name
         -- in the with clauses to find out what the pattern should be.
         -- 'Nothing' means it's the with pattern (so wargn)
         let wargNames 
                 = map Just (reverse (getReq _ withSub)) ++ 
                   Nothing :: reverse (map Just (getNotReq _ withSub))

         log 5 ("With function type: " ++ show wtype ++ " " ++ show wargNames)
         wname <- genWithName defining
         addDef wname (newDef [] wtype Private None)
         let rhs_in = apply (IVar loc wname)
                        (map (maybe wval_raw (IVar loc)) wargNames)
         log 10 ("With function RHS: " ++ show rhs_in)
         (rhs, rhs_erased) <- wrapError (InRHS loc defining) $
             checkTerm elab incase defining env' env prf nest' NONE mode rhs_in reqty
             
         -- Generate new clauses by rewriting the matched arguments
         cs' <- traverse (mkClauseWith 1 wname wargNames lhs_raw_src) cs

         -- Elaborate the new definition here
         let wdef = IDef loc wname cs'
         elab c u i m False env nest wdef

         pure (Just (MkClause env' lhspat rhs, MkClause env' lhspat rhs_erased))
  where
    -- If it's 'KeepCons/SubRefl' in 'outprf', that means it was in the outer
    -- environment so we need to keep it in the same place in the 'with'
    -- function. Hence, turn it to KeepCons whatever
    keepOldEnv : (outprf : SubVars outer vs) -> SubVars vs' vs ->
                 (vs'' : List Name ** SubVars vs'' vs)
    keepOldEnv {vs} SubRefl p = (vs ** SubRefl)
    keepOldEnv {vs} p SubRefl = (vs ** SubRefl)
    keepOldEnv (DropCons p) (DropCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** DropCons rest)
    keepOldEnv (DropCons p) (KeepCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** KeepCons rest)
    keepOldEnv (KeepCons p) (DropCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** KeepCons rest)
    keepOldEnv (KeepCons p) (KeepCons p')
        = let (_ ** rest) = keepOldEnv p p' in
              (_ ** KeepCons rest)

    dropWithArgs : Nat -> RawImp annot -> 
                   Core annot (RawImp annot, List (RawImp annot))
    dropWithArgs Z tm = pure (tm, [])
    dropWithArgs (S k) (IApp _ f arg)
        = do (tm, rest) <- dropWithArgs k f
             pure (tm, arg :: rest)
    -- Shouldn't happen if parsed correctly, but there's no guarantee that
    -- inputs come from parsed source so throw an error.
    dropWithArgs _ _ = throw (GenericMsg loc "Badly formed 'with' clause")

    -- Get the arguments for the rewritten pattern clause of a with by looking
    -- up how the argument names matched
    getArgMatch : RawImp annot -> List (String, RawImp annot) ->
                  Maybe Name -> RawImp annot
    getArgMatch warg ms Nothing = warg
    getArgMatch warg ms (Just (UN n))
        = case lookup n ms of
               Nothing => Implicit loc
               Just tm => tm
    getArgMatch warg ms _ = Implicit loc

    getNewLHS : annot -> (drop : Nat) -> Name -> List (Maybe Name) ->
                RawImp annot -> RawImp annot -> Core annot (RawImp annot)
    getNewLHS ploc drop wname wargnames lhs patlhs
        = do (mlhs, wrest) <- dropWithArgs drop patlhs
             let (warg :: rest) = reverse wrest
                 | _ => throw (GenericMsg loc "Badly formed 'with' clause")
             log 10 $ show lhs ++ " against " ++ show mlhs ++
                     " dropping " ++ show (warg :: rest)
             ms <- getMatch lhs mlhs
             log 10 $ "Matches: " ++ show ms
             let newlhs = apply (IVar ploc wname)
                                (map (getArgMatch warg ms) wargnames ++ rest)
             log 5 $ "New LHS: " ++ show newlhs
             pure newlhs

    -- Rewrite the clauses in the block to use an updated LHS.
    -- 'drop' is the number of additional with arguments we expect (i.e.
    -- the things to drop from the end before matching LHSs)
    mkClauseWith : (drop : Nat) -> Name -> List (Maybe Name) ->
                   RawImp annot -> ImpClause annot -> 
                   Core annot (ImpClause annot)
    mkClauseWith drop wname wargnames lhs (PatClause ploc patlhs rhs)
        = do newlhs <- getNewLHS ploc drop wname wargnames lhs patlhs
             pure (PatClause ploc newlhs rhs)
    mkClauseWith drop wname wargnames lhs (WithClause ploc patlhs rhs ws)
        = do newlhs <- getNewLHS ploc drop wname wargnames lhs patlhs
             ws' <- traverse (mkClauseWith (S drop) wname wargnames lhs) ws
             pure (WithClause ploc newlhs rhs ws')
    mkClauseWith drop wname wargnames lhs (ImpossibleClause ploc patlhs)
        = do newlhs <- getNewLHS ploc drop wname wargnames lhs patlhs
             pure (ImpossibleClause ploc newlhs)

nameListEq : (xs : List Name) -> (ys : List Name) -> Maybe (xs = ys)
nameListEq [] [] = Just Refl
nameListEq (x :: xs) (y :: ys) with (nameEq x y)
  nameListEq (x :: xs) (x :: ys) | (Just Refl) with (nameListEq xs ys)
    nameListEq (x :: xs) (x :: xs) | (Just Refl) | Just Refl= Just Refl
    nameListEq (x :: xs) (x :: ys) | (Just Refl) | Nothing = Nothing
  nameListEq (x :: xs) (y :: ys) | Nothing = Nothing
nameListEq _ _ = Nothing

toPats : (Clause, Clause) -> (List Name, ClosedTerm, ClosedTerm)
toPats (MkClause {vars} env lhs rhs, _) 
    = (vars, bindEnv env lhs, bindEnv env rhs)

export
processDef : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             {auto m : Ref Meta (Metadata annot)} ->
             Reflect annot =>
             Elaborator annot ->
             Bool ->
             Env Term vars -> NestedNames vars -> annot ->
             Name -> List (ImpClause annot) -> 
             Core annot ()
processDef elab incase env nest loc n_in cs_raw
    = do gam <- getCtxt
         n <- inCurrentNS n_in
         case lookupGlobalExact n gam of
              Nothing => throw (NoDeclaration loc n)
              Just glob =>
                case definition glob of
                     None =>
                        do let ty = type glob
                           let hashit = visibility glob == Public
                           let mult = if multiplicity glob == Rig0
                                         then Rig0
                                         else Rig1
                           cs <- traverse (checkClause elab incase mult hashit n env nest) cs_raw
                           (cargs ** tree_comp) <- getPMDef loc n ty (map fst (mapMaybe id cs))
                           (rargs ** tree_rt) <- getPMDef loc n ty (map snd (mapMaybe id cs))
                           
                           let Just Refl = nameListEq cargs rargs
                                   | Nothing => throw (InternalError "WAT")
                           addFnDef loc n tree_comp tree_rt 
                                    (mapMaybe (map toPats) cs)
                           
                           addToSave n
                           gam <- getCtxt
                           log 3 $
                              case lookupDefExact n gam of
                                   Just (PMDef _ args tc tr _) =>
                                      "Case tree for " ++ show n ++ "\n\t" ++
                                      show args ++ " " ++ show tc ++ "\n" ++
                                      "Run time tree\n" ++
                                      show args ++ " " ++ show tr
                                   _ => "No case tree for " ++ show n
                     _ => throw (AlreadyDefined loc n)
