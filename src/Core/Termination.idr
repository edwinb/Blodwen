module Core.Termination

import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT

import Control.Monad.State
import Data.List

%default covering

-- TODO: After the basics, still to handle:
-- case functions
-- 'assert_total'
-- 'assert_smaller'
-- Delay for corecursive calls

mutual
  findSC : Defs -> Env Term vars ->
           List (Nat, Term vars) -> -- LHS args and their position
           Term vars -> -- Right hand side
           List SCCall 
  findSC {vars} defs env pats (Bind n b sc) 
       = findSCbinder b ++
         findSC defs (b :: env) (map (\ (p, tm) => (p, weaken tm)) pats) sc
    where
      findSCbinder : Binder (Term vars) -> List SCCall
      findSCbinder (Let c val ty) = findSC defs env pats val
      findSCbinder b = [] -- only types, no need to look

  findSC defs env pats tm with (unapply tm)
    findSC defs env pats (apply (Ref Func fn) args) | ArgsList 
       = let arity 
                = case lookupTyExact fn (gamma defs) of
                       Just ty => getArity defs [] ty
                       _ => 0 in
             findSCcall defs env pats fn arity args
    -- Just look in the arguments, we already know 'f' isn't a function ref
    findSC defs env pats (apply f args) | ArgsList 
       = concatMap (findSC defs env pats) args

  -- Expand the size change argument list with 'Nothing' to match the given
  -- arity (i.e. the arity of the function we're calling) to ensure that
  -- it's noted that we don't know the size change relationship with the
  -- extra arguments.
  expandToArity : Nat -> List (Maybe (Nat, SizeChange)) -> 
                  List (Maybe (Nat, SizeChange))
  expandToArity Z xs = xs
  expandToArity (S k) (x :: xs) = x :: expandToArity k xs
  expandToArity (S k) [] = Nothing :: expandToArity k []

  -- Return whether first argument is structurally smaller than the second.
  -- TODO: Can't be smaller than a delayed infinite thing
  smaller : Bool -> -- Have we gone under a constructor yet?
            Term vars -> Term vars -> Bool
  smaller inc _ Erased = False -- Never smaller than an erased thing!
  smaller True s t
      = if s == t
           then True
           else smallerArg True s t
  smaller inc s t = smallerArg inc s t

  smallerArg : Bool -> Term vars -> Term vars -> Bool
  smallerArg inc s tm 
      = case getFnArgs tm of
             (Ref (DataCon t a) cn, args) 
                 => any (smaller True s) args
             _ => case s of
                       App f _ => smaller inc f tm -- Higher order recursive argument
                       _ => False

  -- Calculate the size change for the given argument.
  -- i.e., return the size relationship of the given argument with an entry 
  -- in 'pats'; the position in 'pats' and the size change.
  -- Nothing if there is no relation with any of them.
  mkChange : (pats : List (Nat, Term vars)) -> 
             (arg : Term vars) ->
             Maybe (Nat, SizeChange)
  mkChange [] arg = Nothing
  mkChange ((i, parg) :: pats) arg 
      -- TODO: assert_smaller
      = cond [(arg == parg, Just (i, Same)),
              (smaller False arg parg, Just (i, Smaller))]
            (mkChange pats arg)

  findSCcall : Defs -> Env Term vars -> List (Nat, Term vars) ->
               Name -> Nat -> List (Term vars) ->
               List SCCall
  findSCcall defs env pats fn arity args 
      = [MkSCCall fn (expandToArity arity (map (mkChange pats) args))] 
           ++ concatMap (findSC defs env pats) args

-- Remove all laziness annotations which are nothing to do with coinduction,
-- meaning that all only Force/Delay left is to guard coinductive calls.
delazy : Defs -> Term vars -> Term vars
delazy defs tm with (unapply tm)
  delazy defs (apply (Ref nt fn) args) | ArgsList
      = cond
           [(isDelayType fn defs && all notInf args, 
                 takeLast args (Ref Func fn)),
            (isDelay fn defs && all notInf args, 
                 takeLast args (Ref Func fn)),
            (isForce fn defs && all notInf args, 
                 takeLast args (Ref Func fn))]
           (apply (Ref nt fn) (map (delazy defs) args))
    where
      notInf : Term vars -> Bool
      notInf (Ref _ fn') = not (isInfinite fn' defs)
      notInf _ = True

      takeLast : List (Term vars) -> Term vars -> Term vars
      takeLast [] def = def
      takeLast [x] def = delazy defs x
      takeLast (x :: xs) def = takeLast xs def
  delazy defs (apply f args) | ArgsList
      = apply (delazyFn f) (map (delazy defs) args)
    where
      delazyFn : Term vars -> Term vars
      delazyFn (Bind x b sc) = Bind x (map (delazy defs) b) (delazy defs sc)
      delazyFn tm = tm

findCalls : Defs -> (vars ** (Env Term vars, Term vars, Term vars)) -> List SCCall
findCalls defs (_ ** (env, lhs, rhs_in))
   = let pargs = getArgs (delazy defs lhs) 
         rhs = normaliseOpts tcOnly defs env rhs_in in
         findSC defs env 
                (zip (take (length pargs) [0..]) pargs) (delazy defs rhs)

getSC : Defs -> Def -> List SCCall
getSC defs (PMDef _ args _ _ pats) 
   = concatMap (findCalls defs) pats
getSC defs _ = []

export
calculateSizeChange : {auto c : Ref Ctxt Defs} ->
                      annot -> Name -> Core annot (List SCCall)
calculateSizeChange loc n
    = do defs <- get Ctxt
         case lookupGlobalExact n (gamma defs) of
              Nothing => throw (UndefinedName loc n)
              Just def => pure (getSC defs (definition def))

Arg : Type
Arg = Int

firstArg : Arg
firstArg = 0

nextArg : Arg -> Arg
nextArg x = x + 1

initArgs : Nat -> State Arg (List (Maybe (Arg, SizeChange)))
initArgs Z = pure []
initArgs (S k) 
    = do arg <- get
         put (nextArg arg)
         args' <- initArgs k
         pure (Just (arg, Same) :: args')

-- Traverse the size change graph. When we reach a point we've seen before,
-- at least one of the arguments must have got smaller, otherwise it's
-- potentially non-terminating
checkSC : Defs -> 
          Name -> -- function we're checking
          List (Maybe (Arg, SizeChange)) -> -- functions arguments and change
          List (Name, List (Maybe Arg)) -> -- calls we've seen so far
          State Arg Terminating
checkSC defs f args path
   = let pos = (f, map (map fst) args) in
         if pos `elem` path
            then pure $ checkDesc (mapMaybe (map snd) args) path
            else case lookupGlobalExact f (gamma defs) of
                      Nothing => pure IsTerminating
                      Just def => continue (sizeChange def) (pos :: path)
  where
    -- Look for something descending in the list of size changes
    checkDesc : List SizeChange -> List (Name, List (Maybe Arg)) -> Terminating
    checkDesc [] path = NotTerminating (RecPath (reverse (map fst path)))
    checkDesc (Smaller :: _) _ = IsTerminating
    checkDesc (_ :: xs) path = checkDesc xs path

    getPos : List a -> Nat -> Maybe a
    getPos [] _ = Nothing
    getPos (x :: xs) Z = Just x
    getPos (x :: xs) (S k) = getPos xs k

    updateArg : SizeChange -> Maybe (Arg, SizeChange) -> Maybe (Arg, SizeChange)
    updateArg c Nothing = Nothing
    updateArg c arg@(Just (i, Unknown)) = arg
    updateArg Unknown (Just (i, _)) = Just (i, Unknown)
    updateArg c (Just (i, Same)) = Just (i, c)
    updateArg c arg = arg

    mkArgs : List (Maybe (Nat, SizeChange)) -> List (Maybe (Arg, SizeChange))
    mkArgs [] = []
    mkArgs (Nothing :: xs) = Nothing :: mkArgs xs
    mkArgs (Just (pos, c) :: xs)
        = case getPos args pos of
               Nothing => Nothing :: mkArgs xs
               Just arg => updateArg c arg :: mkArgs xs

    checkCall : List (Name, List (Maybe Arg)) -> SCCall -> State Arg Terminating
    checkCall path sc
        = do let inpath = fnCall sc `elem` map fst path
             term <- checkSC defs (fnCall sc) (mkArgs (fnArgs sc)) path
             if not inpath
                then case term of
                       NotTerminating (RecPath _) =>
                          -- might have lost information while assuming this
                          -- was mutually recursive, so start again with new 
                          -- arguments (that is, where we'd start if the
                          -- function was the top level thing we were checking)
                          do args' <- initArgs (length (fnArgs sc))
                             checkSC defs (fnCall sc) args' path
                       t => pure t
                else pure term

    getWorst : Terminating -> List Terminating -> Terminating
    getWorst term [] = term
    getWorst term (IsTerminating :: xs) = getWorst term xs
    getWorst term (Unchecked :: xs) = getWorst Unchecked xs
    getWorst term (bad :: xs) = bad

    continue : List SCCall -> List (Name, List (Maybe Arg)) -> State Arg Terminating
    continue scs path
        = do allTerm <- traverse (checkCall path) scs
             pure (getWorst IsTerminating allTerm)

calcTerminating : {auto c : Ref Ctxt Defs} ->
                  annot -> Name -> Core annot Terminating
calcTerminating loc n 
    = do defs <- get Ctxt
         case lookupTyExact n (gamma defs) of
              Nothing => throw (UndefinedName loc n)
              Just ty => 
                pure $ evalState 
                         (do args <- initArgs (getArity defs [] ty)
                             checkSC defs n args []) firstArg

export
checkTerminating : {auto c : Ref Ctxt Defs} ->
                   annot -> Name -> Core annot Terminating
checkTerminating loc n
    = do tot <- getTotality loc n
         case isTerminating tot of
              Unchecked => 
                 do tot' <- calcTerminating loc n
                    setTerminating loc n tot'
                    pure tot'
              t => pure t
