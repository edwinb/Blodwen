module Core.Unify

import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT
import public Core.UnifyState

import Data.List
import Data.List.Views
import Control.ST
import Control.ST.ImplicitCall

%default covering

public export
interface Unify (tm : List Name -> Type) where
  -- Unify returns a list of names referring to newly added constraints
  unify : CtxtManage m =>
          (ctxt : Var) -> (ustate : Var) ->
          Env Term vars ->
          tm vars -> tm vars -> 
          ST m (List Name) [ctxt ::: Defs, ustate ::: UState]

ufail : CtxtManage m => String -> ST m a []
ufail msg = throw (GenericMsg msg)

unifyArgs : (CtxtManage m, Unify tm, Quote tm) =>
            (ctxt : Var) -> (ustate : Var) ->
            Env Term vars ->
            List (tm vars) -> List (tm vars) ->
            ST m (List Name) [ctxt ::: Defs, ustate ::: UState]
unifyArgs ctxt ustate env [] [] = pure []
unifyArgs ctxt ustate env (cx :: cxs) (cy :: cys)
    = do constr <- unify ctxt ustate env cx cy
         case constr of
              [] => unifyArgs ctxt ustate env cxs cys
              _ => do gam <- getCtxt ctxt
                      c <- addConstraint ctxt ustate
                               (MkSeqConstraint env 
                                   (map (quote gam env) (cx :: cxs))
                                   (map (quote gam env) (cy :: cys)))
                      pure [c]
unifyArgs ctxt ustate env _ _ = ufail ""

postpone : (ctxt : Var) -> (ustate : Var) ->
           Env Term vars ->
           Term vars -> Term vars ->
           ST m (List Name) [ctxt ::: Defs, ustate ::: UState]
postpone ctxt ustate env x y
    = do c <- addConstraint ctxt ustate
                   (MkConstraint env x y)
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
patternEnv : (ctxt : Var) -> (ustate : Var) ->
            Env Term vars -> List (Closure vars) -> 
            ST m (Maybe (newvars ** SubVars newvars vars))
                 [ctxt ::: Defs, ustate ::: UState]
patternEnv ctxt ustate env args
    = do gam <- getCtxt ctxt
         let args' = map (evalClosure gam) args
         case getVars args' of
              Nothing => pure Nothing
              Just vs => pure (Just (toSubVars _ vs))

-- Instantiate a metavariable by binding the variables in 'newvars'
-- and returning the term
-- If the type of the metavariable doesn't have enough arguments, fail, because
-- this wasn't valid for pattern unification
instantiate : CtxtManage m =>
              (ctxt : Var) -> (ustate : Var) ->
              (metavar : Name) -> SubVars newvars vars -> Term newvars ->
              ST m () [ctxt ::: Defs, ustate ::: UState]
instantiate ctxt ustate metavar smvs tm {newvars}
     = do gam <- getCtxt ctxt
          case lookupDefTy metavar gam of
               Nothing => ufail $ "No such metavariable " ++ show metavar
               Just (_, ty) => 
                    case mkRHS [] newvars CompatPre ty 
                             (rewrite appendNilRightNeutral newvars in tm) of
                         Nothing => ufail $ "Can't make solution for " ++ show metavar
                         Just rhs => 
                            do let soln = MkGlobalDef ty Public 
                                               (PMDef [] (STerm rhs))
                               addDef ctxt metavar soln
                               removeHoleName ustate metavar
  where
    mkRHS : (got : List Name) -> (newvars : List Name) ->
            CompatibleVars got rest ->
            Term rest -> Term (newvars ++ got) -> Maybe (Term rest)
    mkRHS got ns cvs ty tm with (snocList ns)
      mkRHS got [] cvs ty tm | Empty = Just (renameVars cvs tm)
      mkRHS got (ns ++ [n]) cvs (Bind x (Pi _ ty) sc) tm | (Snoc rec) 
           = do sc' <- mkRHS (n :: got) ns (CompatExt cvs) sc 
                           (rewrite appendAssociative ns [n] got in tm)
                pure (Bind x (Lam ty) sc')
      -- Run out of variables to bind
      mkRHS got (ns ++ [n]) cvs ty tm | (Snoc rec) = Nothing

mutual
  -- Find holes which are applied to environments which are too big, and
  -- solve them with a new hole applied to only the available arguments.
  -- Essentially what this achieves is moving a hole to an outer scope where
  -- it solution is now usable
  export
  shrinkHoles : CtxtManage m =>
                (ctxt : Var) -> (ustate : Var) ->
                Env Term vars ->
                List (Term vars) -> Term vars ->
                ST m (Term vars) [ctxt ::: Defs, ustate ::: UState]
  shrinkHoles ctxt ustate env args (Bind x (Let val ty) sc) 
      = do val' <- shrinkHoles ctxt ustate env args val
           ty' <- shrinkHoles ctxt ustate env args ty
           sc' <- shrinkHoles ctxt ustate (Let val ty :: env) (map weaken args) sc
           pure (Bind x (Let val' ty') sc')
  shrinkHoles ctxt ustate env args (Bind x b sc) 
      = do let bty = binderType b
           bty' <- shrinkHoles ctxt ustate env args bty
           sc' <- shrinkHoles ctxt ustate (b :: env) (map weaken args) sc
           pure (Bind x (setType b bty') sc')
  shrinkHoles ctxt ustate env args tm with (unapply tm)
    shrinkHoles ctxt ustate env args (apply (Ref Func h) as) | ArgsList 
         = do gam <- getCtxt ctxt
              -- If the hole we're trying to solve (in the call to 'shrinkHoles')
              -- doesn't have enough arguments to be able to pass them to
              -- 'h' here, make a new hole 'sh' which only uses the available
              -- arguments, and solve h with it.
              case lookupDefTy h gam of
                   Just (Hole, ty) => 
                        do sn <- genName ustate "sh"
                           mkSmallerHole ctxt ustate [] ty h as sn args
                   _ => pure (apply (Ref Func h) as)
    shrinkHoles ctxt ustate env args (apply f []) | ArgsList 
         = pure f
    shrinkHoles ctxt ustate env args (apply f as) | ArgsList 
         = do f' <- shrinkHoles ctxt ustate env args f
              as' <- mapST (shrinkHoles ctxt ustate env args) as
              pure (apply f' as')

  -- if 'argPrefix' is a complete valid prefix of 'args', and all the arguments
  -- are local variables, and none of the other arguments in 'args' are
  -- used in the goal type, then create a new hole 'newhole' which takes that
  -- prefix as arguments. 
  -- Then, solve 'oldhole' by applying 'newhole' to 'argPrefix'
  mkSmallerHole : CtxtManage m =>
                  (ctxt : Var) -> (ustate : Var) ->
                  (eqsofar : List (Term vars)) ->
                  (holetype : ClosedTerm) ->
                  (oldhole : Name) ->
                  (args : List (Term vars)) ->
                  (newhole : Name) ->
                  (argPrefix : List (Term vars)) ->
                  ST m (Term vars) [ctxt ::: Defs, ustate ::: UState]
  mkSmallerHole ctxt ustate sofar holetype oldhole 
                              (Local arg :: args) newhole (Local a :: as)
      = if sameVar arg a
           then mkSmallerHole ctxt ustate (sofar ++ [Local a]) holetype oldhole
                              args newhole as
           else pure (apply (Ref Func oldhole) (sofar ++ args))
  -- We have the right number of arguments, so the hole is usable in this
  -- context.
  mkSmallerHole ctxt ustate sofar holetype oldhole [] newhole []
      = pure (apply (Ref Func oldhole) sofar)
  mkSmallerHole ctxt ustate sofar holetype oldhole args newhole []
  -- Reached a prefix of the arguments, so make a new hole applied to 'sofar'
  -- and use it to solve 'oldhole', as long as the omitted arguments aren't
  -- needed for it.
      = case newHoleType sofar holetype of
             Nothing => ufail $ "Can't shrink hole"
             Just defty =>
                do -- Makse smaller hole
                   let hole = MkGlobalDef defty Public Hole
                   addHoleName ustate newhole
                   addDef ctxt newhole hole
                   -- Solve old hole with it
                   case mkOldHoleDef holetype newhole sofar (sofar ++ args) of
                        Nothing => ufail $ "Can't shrink hole"
                        Just olddef =>
                           do let soln = MkGlobalDef defty Public
                                              (PMDef [] (STerm olddef))
                              addDef ctxt oldhole soln
                              removeHoleName ustate oldhole
                              pure (apply (Ref Func newhole) sofar)
  -- Default case, leave the hole application as it is
  mkSmallerHole ctxt ustate sofar holetype oldhole args _ _
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
           pure (Bind x (Lam ty) sc')
  mkOldHoleDef {hargs} {vars} ty newh sofar args
      = do compat <- areVarsCompatible vars hargs
           let newargs = map (renameVars compat) sofar
           pure (apply (Ref Func newh) newargs)

  unifyApp : CtxtManage m =>
             (ctxt : Var) -> (ustate : Var) ->
             Env Term vars ->
             NHead vars -> List (Closure vars) -> NF vars ->
             ST m (List Name) [ctxt ::: Defs, ustate ::: UState]
  unifyApp ctxt ustate {vars} env (NRef nt var) args tm 
      = case !(patternEnv ctxt ustate env args) of
           Just (newvars ** submv) =>
                do gam <- getCtxt ctxt
                   tm' <- shrinkHoles ctxt ustate env (map (quote gam env) args) 
                                                      (quote gam env tm)
                   gam <- getCtxt ctxt
                   -- newvars and args should be the same length now, because
                   -- there's one new variable for each distinct argument.
                   -- The types don't express this, but 'submv' at least
                   -- tells us that 'newvars' are the subset of 'vars'
                   -- being applied to the metavariable, and so 'tm' must
                   -- only use those variables for success
                   case shrinkTerm tm' submv of
                        Nothing => 
                             ufail $ "Scope error " ++
                                   show (vars, newvars) ++
                                   "\nUnifying " ++
                                   show (quote empty env
                                           (NApp (NRef nt var) args)) ++
                                   " and "
                                   ++ show (quote empty env tm)
                        Just tm' => do instantiate ctxt ustate var submv tm'
                                       pure []
           Nothing => postpone ctxt ustate env 
                         (quote empty env (NApp (NRef nt var) args))
                         (quote empty env tm)
  unifyApp ctxt ustate env hd args (NApp hd' args')
      = postpone ctxt ustate env
                 (quote empty env (NApp hd args)) 
                 (quote empty env (NApp hd' args'))
  -- If they're already convertible without metavariables, we're done,
  -- otherwise postpone
  unifyApp ctxt ustate env hd args tm 
      = do gam <- getCtxt ctxt
           if convert gam env (quote empty env (NApp hd args))
                              (quote empty env tm)
              then pure []
              else postpone ctxt ustate env
                         (quote empty env (NApp hd args)) (quote empty env tm)

  export
  Unify Closure where
    unify ctxt ustate env x y 
        = do gam <- getCtxt ctxt
             -- 'quote' using an empty global context, because then function
             -- names won't reduce until they have to
             let x' = quote empty env x
             let y' = quote empty env y
             unify ctxt ustate env x' y'

  export
  Unify NF where
    unify ctxt ustate env (NBind x (Pi ix tx) scx) (NBind y (Pi iy ty) scy) 
        = if ix /= iy
             then ufail $ "Can't unify " ++ show (quote empty env
                                                     (NBind x (Pi ix tx) scx))
                                         ++ " and " ++
                                            show (quote empty env
                                                     (NBind y (Pi iy ty) scy))
             else
               do ct <- unify ctxt ustate env tx ty
                  xn <- genName ustate "x"
                  let env' : TT.Env.Env Term (x :: _)
                           = Pi ix (quote empty env tx) :: env
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
                                c <- addConstant ctxt ustate env
                                       (Bind x (Lam txtm) (Local Here))
                                       (Bind x (Pi Explicit txtm)
                                           (weaken tytm)) cs
                                let tscx = scx (toClosure env (Ref Bound xn))
                                let tscy = scy (toClosure env 
                                               (App (mkConstantApp c env) (Ref Bound xn)))
                                let termx = refToLocal xn x (quote empty env tscx)
                                let termy = refToLocal xn x (quote empty env tscy)
                                cs' <- unify ctxt ustate env' termx termy
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
                          c <- addConstant ctxt ustate env
                                 (Bind x (Lam txtm) (Local Here))
                                 (Bind x (Pi Explicit txtm)
                                     (weaken tytm)) cs
                          let tscx = scx (toClosure env (Ref Bound xn))
                          let tscy = scy (toClosure env 
                                         (App (mkConstantApp c env) (Ref Bound xn)))
                          let termx = refToLocal xn x (quote empty env tscx)
                          let termy = refToLocal xn x (quote empty env tscy)
                          cs' <- unify ctxt ustate env' termx termy
                          pure (union cs cs')
-}
    unify ctxt ustate env y (NApp hd args)
        = unifyApp ctxt ustate env hd args y
    unify ctxt ustate env (NApp hd args) y 
        = unifyApp ctxt ustate env hd args y
    unify ctxt ustate env (NDCon x tagx ax xs) (NDCon y tagy ay ys)
        = if tagx == tagy
             then unifyArgs ctxt ustate env xs ys
             else ufail $ "Can't unify " ++ show (quote empty env
                                                        (NDCon x tagx ax xs))
                                         ++ " and "
                                         ++ show (quote empty env
                                                        (NDCon y tagy ay ys))
    unify ctxt ustate env (NTCon x tagx ax xs) (NTCon y tagy ay ys)
        = if tagx == tagy
             then unifyArgs ctxt ustate env xs ys
             else ufail $ "Can't unify " ++ show (quote empty env
                                                        (NTCon x tagx ax xs))
                                         ++ " and "
                                         ++ show (quote empty env
                                                        (NTCon y tagy ay ys))
    unify ctxt ustate env (NPrimVal x) (NPrimVal y) 
        = if x == y 
             then pure [] 
             else ufail $ "Can't unify " ++ show x ++ " and " ++ show y
    unify ctxt ustate env x NErased = pure []
    unify ctxt ustate env NErased y = pure []
    unify ctxt ustate env NType NType = pure []
    unify ctxt ustate env x y 
        = do gam <- getCtxt ctxt
             if convert gam env x y
                then pure []
                else ufail $ "Can't unify " ++ show (quote empty env x)
                                            ++ " and "
                                            ++ show (quote empty env y)

  export
  Unify Term where
    -- TODO: Don't just go to values, try to unify the terms directly
    -- and avoid normalisation as far as possible
    unify ctxt ustate env x y 
          = do gam <- getCtxt ctxt
               unify ctxt ustate env (nf gam env x) (nf gam env y)

-- Try again to solve the given named constraint, and return the list
-- of constraint names are generated when trying to solve it.
export
retry : CtxtManage m =>
        (ctxt : Var) -> (ustate : Var) ->
        (cname : Name) -> ST m (List Name) [ctxt ::: Defs, ustate ::: UState]
retry ctxt ustate cname
    = do ust <- read ustate
         case lookupCtxt cname (constraints ust) of
              Nothing => throw (GenericMsg ("No such constraint " ++ show cname))
              -- If the constraint is now resolved (i.e. unifying now leads
              -- to no new constraints) replace it with 'Resolved' in the
              -- constraint context so we don't do it again
              Just Resolved => pure []
              Just (MkConstraint env x y) =>
                   do cs <- unify ctxt ustate env x y
                      case cs of
                           [] => do setConstraint ustate cname Resolved
                                    pure cs
                           _ => pure cs
              Just (MkSeqConstraint env xs ys) =>
                   do cs <- unifyArgs ctxt ustate env xs ys
                      case cs of
                           [] => do setConstraint ustate cname Resolved
                                    pure cs
                           _ => pure cs

retryHole : CtxtManage m =>
            (ctxt : Var) -> (ustate : Var) ->
            (hole : Name) ->
            ST m () [ctxt ::: Defs, ustate ::: UState]
retryHole ctxt ustate hole
    = do gam <- getCtxt ctxt
         case lookupDef hole gam of
              Nothing => throw (GenericMsg ("No such hole " ++ show hole))
              Just (Guess tm constraints) => 
                   do cs' <- mapST (retry ctxt ustate) constraints
                      case concat cs' of
                           -- All constraints resolved, so turn into a
                           -- proper definition and remove it from the
                           -- hole list
                           [] => do updateDef ctxt hole (PMDef [] (STerm tm))
                                    removeHoleName ustate hole
                           newcs => updateDef ctxt hole (Guess tm newcs)
              Just _ => pure () -- Nothing we can do

-- Attempt to solve any remaining constraints in the unification context.
-- Do this by working through the list of holes
-- On encountering a 'Guess', try the constraints attached to it 
export
solveConstraints : CtxtManage m =>
                   (ctxt : Var) -> (ustate : Var) ->
                   ST m () [ctxt ::: Defs, ustate ::: UState]
solveConstraints ctxt ustate 
    = do hs <- getHoleNames ustate
         mapST (retryHole ctxt ustate) hs
         -- Question: Another iteration if any holes have been resolved?
         pure ()

dumpHole : CtxtManage m =>
           (ctxt : Var) -> (ustate : Var) ->
           (hole : Name) ->
           ST m () [ctxt ::: Defs, ustate ::: UState]
dumpHole ctxt ustate hole
    = do gam <- getCtxt ctxt
         case lookupDefTy hole gam of
              Nothing => throw (GenericMsg ("No such hole " ++ show hole))
              Just (Guess tm constraints, ty) => 
                   do putStrLn $ "!" ++ show hole ++ " : " ++ 
                                        show (normalise gam [] ty)
                      mapST dumpConstraint constraints 
                      pure ()
              Just (PMDef args t, ty) =>
                   putStrLn $ "Solved: " ++ show hole ++ " : " ++ 
                                 show (normalise gam [] ty) ++
                                 " = " ++ show t
              Just (_, ty) =>
                   putStrLn $ "?" ++ show hole ++ " : " ++ 
                                     show (normalise gam [] ty)
  where
    dumpConstraint : ConsoleIO m => Name -> ST m () [ctxt ::: Defs, ustate ::: UState]
    dumpConstraint n
        = do ust <- read ustate
             gam <- getCtxt ctxt
             case lookupCtxt n (constraints ust) of
                  Nothing => pure ()
                  Just Resolved => putStrLn "\tResolved"
                  Just (MkConstraint env x y) =>
                       putStrLn $ "\t" ++ show (normalise gam env x) 
                                      ++ " =?= " ++ show (normalise gam env y)
                  Just (MkSeqConstraint _ xs ys) =>
                       putStrLn $ "\t" ++ show xs ++ " =?= " ++ show ys

export
dumpConstraints : CtxtManage m =>
                  (ctxt : Var) -> (ustate : Var) ->
                  ST m () [ctxt ::: Defs, ustate ::: UState]
dumpConstraints ctxt ustate
    = do hs <- getCurrentHoleNames ustate
         mapST (dumpHole ctxt ustate) hs
         pure ()

