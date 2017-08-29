module Core.Unify

import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT
import public Core.UnifyState

import Data.List
import Data.List.Views

%default covering

public export
interface Unify (tm : List Name -> Type) where
  -- Unify returns a list of names referring to newly added constraints
  unify : annot -> Env Term vars ->
          tm vars -> tm vars -> 
          Core annot [Ctxt ::: Defs, UST ::: UState annot] (List Name)

ufail : annot -> String -> Core annot [] a
ufail loc msg = throw (GenericMsg loc msg)

unifyArgs : (Unify tm, Quote tm) =>
            annot -> Env Term vars ->
            List (tm vars) -> List (tm vars) ->
            Core annot [Ctxt ::: Defs, UST ::: UState annot] (List Name)
unifyArgs loc env [] [] = pure []
unifyArgs loc env (cx :: cxs) (cy :: cys)
    = do constr <- unify loc env cx cy
         case constr of
              [] => unifyArgs loc env cxs cys
              _ => do gam <- getCtxt 
                      cs <- unifyArgs loc env cxs cys
                      -- TODO: Fix this bit! See p59 Ulf's thesis
--                       c <- addConstraint 
--                                (MkSeqConstraint loc env 
--                                    (map (quote gam env) (cx :: cxs))
--                                    (map (quote gam env) (cy :: cys)))
                      pure (union constr cs) -- [c]
unifyArgs loc env _ _ = ufail loc ""

postpone : annot -> Env Term vars ->
           Term vars -> Term vars ->
           Core annot [Ctxt ::: Defs, UST ::: UState annot] (List Name)
postpone loc env x y
    = do c <- addConstraint (MkConstraint loc env x y)
         pure [c]

-- Get the variables in an application argument list; fail if any arguments 
-- are not variables, fail if there's any repetition of variables
-- We use this to check that the pattern unification rule is applicable
-- when solving a metavariable applied to arguments
getVars : List (NF vars) -> Maybe (List (x ** Elem x vars))
getVars [] = Just []
getVars (NApp (NLocal v) [] :: xs) 
    = if vIn xs then Nothing
         else do xs' <- getVars xs
                 pure ((_ ** v) :: xs')
  where
    -- Check the variable doesn't appear later
    vIn : List (NF vars) -> Bool
    vIn [] = False
    vIn (NApp (NLocal el') [] :: xs)
        = if sameVar v el' then True else vIn xs
    vIn (_ :: xs) = vIn xs
getVars (_ :: xs) = Nothing

-- Make a sublist representing the variables used in the application.
-- We'll use this to ensure that local variables which appear in a term
-- are all arguments to a metavariable application for pattern unification
toSubVars : (vars : List Name) -> List (x ** Elem x vars) ->
            (newvars ** SubVars newvars vars)
toSubVars [] xs = ([] ** SubRefl)
toSubVars (n :: ns) xs 
     -- If there's a proof 'Here' in 'xs', then 'n' should be kept,
     -- otherwise dropped
     -- (Remember: 'n' might be shadowed; looking for 'Here' ensures we
     -- get the *right* proof that the name is in scope!)
     = let (_ ** svs) = toSubVars ns (dropHere xs) in
           if anyHere xs 
              then (_ ** KeepCons svs)
              else (_ ** DropCons svs)
  where
    anyHere : List (x ** Elem x (n :: ns)) -> Bool
    anyHere [] = False
    anyHere ((_ ** Here) :: xs) = True
    anyHere ((_ ** There p) :: xs) = anyHere xs

    dropHere : List (x ** Elem x (n :: ns)) -> List (x ** Elem x ns) 
    dropHere [] = []
    dropHere ((_ ** Here) :: xs) = dropHere xs
    dropHere ((_ ** There p) :: xs) = (_ ** p) :: dropHere xs

{- Applying the pattern unification rule is okay if:
   * Arguments are all distinct local variables
   * The metavariable name doesn't appear in the unifying term
   * The local variables which appear in the term are all arguments to
     the metavariable application (not checked here, checked with the
     result of `patternEnv`

   Return the subset of the environment used in the arguments
   to which the metavariable is applied. If this environment is enough
   to check the term we're unifying with, and that term doesn't use the
   metavariable name, we can safely apply the rule.
-}
patternEnv : Env Term vars -> List (Closure vars) -> 
             Core annot [Ctxt ::: Defs, UST ::: UState annot]
                  (Maybe (newvars ** SubVars newvars vars))
patternEnv env args
    = do gam <- getCtxt
         let args' = map (evalClosure gam) args
         case getVars args' of
              Nothing => pure Nothing
              Just vs => pure (Just (toSubVars _ vs))

-- Instantiate a metavariable by binding the variables in 'newvars'
-- and returning the term
-- If the type of the metavariable doesn't have enough arguments, fail, because
-- this wasn't valid for pattern unification
instantiate : annot ->
              (metavar : Name) -> SubVars newvars vars -> Term newvars ->
              Core annot [Ctxt ::: Defs, UST ::: UState annot] ()
instantiate loc metavar smvs tm {newvars}
     = do gam <- getCtxt
          case lookupDefTy metavar gam of
               Nothing => ufail loc $ "No such metavariable " ++ show metavar
               Just (_, ty) => 
                    case mkRHS [] newvars CompatPre ty 
                             (rewrite appendNilRightNeutral newvars in tm) of
                         Nothing => ufail loc $ "Can't make solution for " ++ show metavar
                         Just rhs => 
                            do let soln = newDef ty Public 
                                               (PMDef True [] (STerm rhs))
                               addDef metavar soln
                               removeHoleName metavar
  where
    mkRHS : (got : List Name) -> (newvars : List Name) ->
            CompatibleVars got rest ->
            Term rest -> Term (newvars ++ got) -> Maybe (Term rest)
    mkRHS got ns cvs ty tm with (snocList ns)
      mkRHS got [] cvs ty tm | Empty = Just (renameVars cvs tm)
      mkRHS got (ns ++ [n]) cvs (Bind x (Pi _ ty) sc) tm | (Snoc rec) 
           = do sc' <- mkRHS (n :: got) ns (CompatExt cvs) sc 
                           (rewrite appendAssociative ns [n] got in tm)
                pure (Bind x (Lam Explicit ty) sc')
      -- Run out of variables to bind
      mkRHS got (ns ++ [n]) cvs ty tm | (Snoc rec) = Nothing

export
implicitBind : Name -> Core annot [Ctxt ::: Defs, UST ::: UState annot] ()
implicitBind n = updateDef n ImpBind

-- Check that the references in the term are defined before the given
-- creation time (essentially this checks that there's no cycles in hole
-- solutions, i.e. that holes are defined in terms of previously defined
-- things, which subsumes the occurs check)
occursCheck : Name -> Term vars -> Bool
occursCheck hole (Ref nt var)
    = hole /= var
occursCheck hole (Bind n (Let val ty) sc)
      = occursCheck hole val && occursCheck hole ty && occursCheck hole sc
occursCheck hole (Bind n b sc)
      = occursCheck hole (binderType b) && occursCheck hole sc
occursCheck hole tm with (unapply tm)
  occursCheck hole (apply f []) | ArgsList = True -- won't be Ref, matched above
  occursCheck hole (apply f args) | ArgsList 
      = occursCheck hole f && and (map (\a => occursCheck hole a) args)

mutual
  -- Find holes which are applied to environments which are too big, and
  -- solve them with a new hole applied to only the available arguments.
  -- Essentially what this achieves is moving a hole to an outer scope where
  -- it solution is now usable
  export
  shrinkHoles : annot -> Env Term vars ->
                List (Term vars) -> Term vars ->
                Core annot [Ctxt ::: Defs, UST ::: UState annot] (Term vars)
  shrinkHoles loc env args (Bind x (Let val ty) sc) 
      = do val' <- shrinkHoles loc env args val
           ty' <- shrinkHoles loc env args ty
           sc' <- shrinkHoles loc (Let val ty :: env) (map weaken args) sc
           pure (Bind x (Let val' ty') sc')
  shrinkHoles loc env args (Bind x b sc) 
      = do let bty = binderType b
           bty' <- shrinkHoles loc env args bty
           sc' <- shrinkHoles loc (b :: env) (map weaken args) sc
           pure (Bind x (setType b bty') sc')
  shrinkHoles loc env args tm with (unapply tm)
    shrinkHoles loc env args (apply (Ref Func h) as) | ArgsList 
         = do gam <- getCtxt
              -- If the hole we're trying to solve (in the call to 'shrinkHoles')
              -- doesn't have enough arguments to be able to pass them to
              -- 'h' here, make a new hole 'sh' which only uses the available
              -- arguments, and solve h with it.
              case lookupDefTy h gam of
                   Just (Hole, ty) => 
                        do sn <- genName "sh"
                           mkSmallerHole loc [] ty h as sn args
                   _ => pure (apply (Ref Func h) as)
    shrinkHoles loc env args (apply f []) | ArgsList 
         = pure f
    shrinkHoles loc env args (apply f as) | ArgsList 
         = do f' <- shrinkHoles loc env args f
              as' <- traverse (\x => shrinkHoles loc env args x) as
              pure (apply f' as')

  -- if 'argPrefix' is a complete valid prefix of 'args', and all the arguments
  -- are local variables, and none of the other arguments in 'args' are
  -- used in the goal type, then create a new hole 'newhole' which takes that
  -- prefix as arguments. 
  -- Then, solve 'oldhole' by applying 'newhole' to 'argPrefix'
  mkSmallerHole : annot ->
                  (eqsofar : List (Term vars)) ->
                  (holetype : ClosedTerm) ->
                  (oldhole : Name) ->
                  (args : List (Term vars)) ->
                  (newhole : Name) ->
                  (argPrefix : List (Term vars)) ->
                  Core annot [Ctxt ::: Defs, UST ::: UState annot] (Term vars)
  mkSmallerHole loc sofar holetype oldhole 
                              (Local arg :: args) newhole (Local a :: as)
      = if sameVar arg a
           then mkSmallerHole loc (sofar ++ [Local a]) holetype oldhole
                              args newhole as
           else pure (apply (Ref Func oldhole) (sofar ++ args))
  -- We have the right number of arguments, so the hole is usable in this
  -- context.
  mkSmallerHole loc sofar holetype oldhole [] newhole []
      = pure (apply (Ref Func oldhole) sofar)
  mkSmallerHole loc sofar holetype oldhole args newhole []
  -- Reached a prefix of the arguments, so make a new hole applied to 'sofar'
  -- and use it to solve 'oldhole', as long as the omitted arguments aren't
  -- needed for it.
      = case newHoleType sofar holetype of
             Nothing => ufail loc $ "Can't shrink hole"
             Just defty =>
                do -- Make smaller hole
                   let hole = newDef defty Public (Hole (length sofar))
                   addHoleName newhole
                   addDef newhole hole
                   -- Solve old hole with it
                   case mkOldHoleDef holetype newhole sofar (sofar ++ args) of
                        Nothing => ufail loc $ "Can't shrink hole"
                        Just olddef =>
                           do let soln = newDef defty Public
                                              (PMDef True [] (STerm olddef))
                              addDef oldhole soln
                              removeHoleName oldhole
                              pure (apply (Ref Func newhole) sofar)
  -- Default case, leave the hole application as it is
  mkSmallerHole loc sofar holetype oldhole args _ _
      = pure (apply (Ref Func oldhole) (sofar ++ args))

  -- Drop the pi binders from the front of a term. This is only valid if
  -- the name is not used in the scope
  dropBinders : SubVars vars (drop ++ vars) -> 
                Term (drop ++ vars) -> Maybe (Term vars)
  dropBinders {drop} subprf (Bind n (Pi imp ty) scope)
    = dropBinders {drop = n :: drop} (DropCons subprf) scope
  dropBinders subprf tm = shrinkTerm tm subprf

  newHoleType : List (Term vars) -> Term hvars -> Maybe (Term hvars)
  newHoleType [] tm = dropBinders {drop = []} SubRefl tm
  newHoleType (x :: xs) (Bind n (Pi imp ty) scope) 
      = do scope' <- newHoleType xs scope
           pure (Bind n (Pi imp ty) scope')
  newHoleType _ _ = Nothing

  mkOldHoleDef : Term hargs -> Name ->
                 List (Term vars) -> List (Term vars) ->
                 Maybe (Term hargs)
  mkOldHoleDef (Bind x (Pi _ ty) sc) newh sofar (a :: args)
      = do sc' <- mkOldHoleDef sc newh sofar args
           pure (Bind x (Lam Explicit ty) sc')
  mkOldHoleDef {hargs} {vars} ty newh sofar args
      = do compat <- areVarsCompatible vars hargs
           let newargs = map (renameVars compat) sofar
           pure (apply (Ref Func newh) newargs)
  
  isHoleNF : Gamma -> Name -> Bool
  isHoleNF gam n
      = case lookupDef n gam of
             Just (Hole _) => True
             _ => False

  unifyHole : annot -> Env Term vars ->
              NameType -> Name -> List (Closure vars) -> NF vars ->
              Core annot [Ctxt ::: Defs, UST ::: UState annot] (List Name)
  unifyHole loc env nt var args tm
      = case !(patternEnv env args) of
           Just (newvars ** submv) =>
                do gam <- getCtxt
--                    tm' <- shrinkHoles loc env (map (quote gam env) args) 
--                                               (quote gam env tm)
--                    gam <- getCtxt
                   -- newvars and args should be the same length now, because
                   -- there's one new variable for each distinct argument.
                   -- The types don't express this, but 'submv' at least
                   -- tells us that 'newvars' are the subset of 'vars'
                   -- being applied to the metavariable, and so 'tm' must
                   -- only use those variables for success
                   case shrinkTerm (quote gam env tm) submv of
                        Nothing => do
                           postpone loc env 
                             (quote empty env (NApp (NRef nt var) args))
                             (quote empty env tm)
--                              ufail loc $ "Scope error " ++
--                                    show (vars, newvars) ++
--                                    "\nUnifying " ++
--                                    show (quote gam env
--                                            (NApp (NRef nt var) args)) ++
--                                    " and "
--                                    ++ show (quote gam env tm)
                        Just tm' => 
                            -- if the terms are the same, this isn't a solution
                            -- but they are already unifying, so just return
                            if convert gam env (NApp (NRef nt var) args) tm
                               then pure []
                               else
                                -- otherwise, instantiate the hole
                                   if not (occursCheck var tm')
                                      then throw (Cycle loc env
                                                 (quote empty env (NApp (NRef nt var) args))
                                                 (quote empty env tm))
                                      else do instantiate loc var submv tm'
                                              pure []
           Nothing => postpone loc env 
                           (quote empty env (NApp (NRef nt var) args))
                           (quote empty env tm)

  unifyApp : annot -> Env Term vars ->
             NHead vars -> List (Closure vars) -> NF vars ->
             Core annot [Ctxt ::: Defs, UST ::: UState annot] (List Name)
  unifyApp loc env (NRef nt var) args tm 
      = do gam <- getCtxt
           if isHoleNF gam var
              then unifyHole loc env nt var args tm
              else unifyIfEq True loc env (NApp (NRef nt var) args) tm
  unifyApp loc env (NLocal x) [] (NApp (NLocal y) [])
      = if sameVar x y then pure []
           else postpone loc env
                     (quote empty env (NApp (NLocal x) [])) 
                     (quote empty env (NApp (NLocal y) []))
  unifyApp loc env hd args (NApp hd' args')
      = postpone loc env
                 (quote empty env (NApp hd args)) 
                 (quote empty env (NApp hd' args'))
  -- If they're already convertible without metavariables, we're done,
  -- otherwise postpone
  unifyApp loc env hd args tm 
      = do gam <- getCtxt
           if convert gam env (quote empty env (NApp hd args))
                              (quote empty env tm)
              then pure []
              else postpone loc env
                         (quote empty env (NApp hd args)) (quote empty env tm)
  
  export
  Unify Closure where
    unify loc env x y 
        = do gam <- getCtxt
             -- 'quote' using an empty global context, because then function
             -- names won't reduce until they have to
             let x' = quote empty env x
             let y' = quote empty env y
             unify loc env x' y'

  unifyIfEq : (postpone : Bool) ->
              annot -> Env Term vars -> NF vars -> NF vars -> 
                  Core annot [Ctxt ::: Defs, UST ::: UState annot] (List Name)
  unifyIfEq post loc env x y 
        = do gam <- getCtxt
             if convert gam env x y
                then pure []
                else if post 
                        then postpone loc env (quote empty env x) (quote empty env y)
                        else ufail loc $ "Can't unify " ++ show (quote empty env x)
                                            ++ " and "
                                            ++ show (quote empty env y)

  export
  Unify NF where
    unify loc env (NBind x (Pi ix tx) scx) (NBind y (Pi iy ty) scy) 
        = if ix /= iy
             then ufail loc $ "Can't unify " ++ show (quote empty env
                                                     (NBind x (Pi ix tx) scx))
                                         ++ " and " ++
                                            show (quote empty env
                                                     (NBind y (Pi iy ty) scy))
             else
               do ct <- unify loc env tx ty
                  xn <- genName "x"
                  let env' : TT.Env.Env Term (x :: _)
                           = Pi ix (quote empty env tx) :: env
                  case ct of
                       [] => -- no constraints, check the scope
                             do let tscx = scx (toClosure env (Ref Bound xn))
                                let tscy = scy (toClosure env (Ref Bound xn))
                                let termx = refToLocal xn x (quote empty env tscx)
                                let termy = refToLocal xn x (quote empty env tscy)
                                unify loc env' termx termy
                       cs => -- constraints, make new guarded constant
                             do let txtm = quote empty env tx
                                let tytm = quote empty env ty
                                c <- addConstant env
                                       (Bind x (Lam Explicit txtm) (Local Here))
                                       (Bind x (Pi Explicit txtm)
                                           (weaken tytm)) cs
                                let tscx = scx (toClosure env (Ref Bound xn))
                                let tscy = scy (toClosure env 
                                               (App (mkConstantApp c env) (Ref Bound xn)))
                                let termx = refToLocal xn x (quote empty env tscx)
                                let termy = refToLocal xn x (quote empty env tscy)
                                cs' <- unify loc env' termx termy
                                pure (union cs cs')
{- -- probably not...
    unify ctxt ustate env (NBind x (Lam tx) scx) (NBind y (Lam ty) scy) 
       = do ct <- unify ctxt ustate env tx ty
            xn <- genName ustate "x"
            let env' : TT.Env.Env Term (x :: _)
                     = Lam (quote empty env tx) :: env
            case ct of
                 [] => -- no constraints, check the scope
                       do let tscx = scx (toClosure env (Ref Bound xn))
                          let tscy = scy (toClosure env (Ref Bound xn))
                          let termx = refToLocal xn x (quote empty env tscx)
                          let termy = refToLocal xn x (quote empty env tscy)
                          unify ctxt ustate env' termx termy
                 cs => -- constraints, make new guarded constant
                       do let txtm = quote empty env tx
                          let tytm = quote empty env ty
                          c <- addConstant env
                                 (Bind x (Lam txtm) (Local Here))
                                 (Bind x (Pi Explicit txtm)
                                     (weaken tytm)) cs
                          let tscx = scx (toClosure env (Ref Bound xn))
                          let tscy = scy (toClosure env 
                                         (App (mkConstantApp c env) (Ref Bound xn)))
                          let termx = refToLocal xn x (quote empty env tscx)
                          let termy = refToLocal xn x (quote empty env tscy)
                          cs' <- unify env' termx termy
                          pure (union cs cs')
-}
    -- If they're both holes, solve the one with the bigger context with
    -- the other
    unify loc env (NApp (NRef xt hdx) argsx) (NApp (NRef yt hdy) argsy)
        = do gam <- getCtxt
             if isHoleNF gam hdx && isHoleNF gam hdy
                then
                   (if length argsx > length argsy
                       then unifyApp loc env (NRef xt hdx) argsx 
                                             (NApp (NRef yt hdy) argsy)
                       else unifyApp loc env (NRef yt hdy) argsy 
                                             (NApp (NRef xt hdx) argsx))
                else 
                   (if isHoleNF gam hdx
                       then unifyApp loc env (NRef xt hdx) argsx
                                             (NApp (NRef yt hdy) argsy)
                       else unifyApp loc env (NRef yt hdy) argsy 
                                             (NApp (NRef xt hdx) argsx))
    unify loc env y (NApp hd args)
        = unifyApp loc env hd args y
    unify loc env (NApp hd args) y 
        = unifyApp loc env hd args y
    unify loc env (NDCon x tagx ax xs) (NDCon y tagy ay ys)
        = if tagx == tagy
             then unifyArgs loc env xs ys
             else ufail loc $ "Can't unify " ++ show (quote empty env
                                                        (NDCon x tagx ax xs))
                                         ++ " and "
                                         ++ show (quote empty env
                                                        (NDCon y tagy ay ys))
    unify loc env (NTCon x tagx ax xs) (NTCon y tagy ay ys)
        = if tagx == tagy
             then unifyArgs loc env xs ys
             else ufail loc $ "Can't unify " ++ show (quote empty env
                                                        (NTCon x tagx ax xs))
                                         ++ " and "
                                         ++ show (quote empty env
                                                        (NTCon y tagy ay ys))
    unify loc env (NPrimVal x) (NPrimVal y) 
        = if x == y 
             then pure [] 
             else ufail loc $ "Can't unify " ++ show x ++ " and " ++ show y
    unify loc env x NErased = pure []
    unify loc env NErased y = pure []
    unify loc env NType NType = pure []
    unify loc env x y = unifyIfEq False loc env x y

  export
  Unify Term where
    -- TODO: Don't just go to values, try to unify the terms directly
    -- and avoid normalisation as far as possible
    unify loc env x y 
          = do gam <- getCtxt
               unify loc env (nf gam env x) (nf gam env y)

-- Try again to solve the given named constraint, and return the list
-- of constraint names are generated when trying to solve it.
export
retry : (cname : Name) -> 
        Core annot [Ctxt ::: Defs, UST ::: UState annot] (List Name)
retry cname
    = do ust <- get UST
         case lookupCtxt cname (constraints ust) of
              Nothing => pure []
              -- If the constraint is now resolved (i.e. unifying now leads
              -- to no new constraints) replace it with 'Resolved' in the
              -- constraint context so we don't do it again
              Just Resolved => pure []
              Just (MkConstraint loc env x y) =>
                   do cs <- unify loc env x y
                      case cs of
                           [] => do setConstraint cname Resolved
                                    pure []
                           _ => pure cs
              Just (MkSeqConstraint loc env xs ys) =>
                   do cs <- unifyArgs loc env xs ys
                      case cs of
                           [] => do setConstraint cname Resolved
                                    pure []
                           _ => pure cs

retryHole : (hole : Name) ->
            Core annot [Ctxt ::: Defs, UST ::: UState annot] ()
retryHole hole
    = do gam <- getCtxt
         case lookupDef hole gam of
              Nothing => pure ()
              Just (Guess tm constraints) => 
                   do cs' <- traverse (\x => retry x) constraints
                      case concat cs' of
                           -- All constraints resolved, so turn into a
                           -- proper definition and remove it from the
                           -- hole list
                           [] => do updateDef hole (PMDef True [] (STerm tm))
                                    removeHoleName hole
                           newcs => updateDef hole (Guess tm newcs)
              Just _ => pure () -- Nothing we can do

-- Attempt to solve any remaining constraints in the unification context.
-- Do this by working through the list of holes
-- On encountering a 'Guess', try the constraints attached to it 
export
solveConstraints : Core annot [Ctxt ::: Defs, UST ::: UState annot] ()
solveConstraints 
    = do hs <- getHoleNames
         traverse (\x => retryHole x) hs
         -- Question: Another iteration if any holes have been resolved?
         pure ()

