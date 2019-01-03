module Core.Termination

import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT

import Control.Monad.State
import Data.List

import Debug.Trace

%default covering

data Guardedness = Toplevel | Unguarded | Guarded | InDelay

mutual
  findSC : Defs -> Env Term vars -> Guardedness ->
           List (Nat, Term vars) -> -- LHS args and their position
           Term vars -> -- Right hand side
           List SCCall 
  findSC {vars} defs env g pats (Bind n b sc) 
       = findSCbinder b ++
         findSC defs (b :: env) g (map (\ (p, tm) => (p, weaken tm)) pats) sc
    where
      findSCbinder : Binder (Term vars) -> List SCCall
      findSCbinder (Let c val ty) = findSC defs env g pats val
      findSCbinder b = [] -- only types, no need to look

  findSC defs env g pats tm with (unapply tm)
    -- If we're InDelay and find a constructor (or a function call which is
    -- guaranteed to return a constructor; AllGuarded set), continue as InDelay
    findSC defs env InDelay pats (apply (Ref (DataCon _ _) _) args) | ArgsList
       = concatMap (findSC defs env InDelay pats) args
    -- If we're InDelay otherwise, just check the arguments
    findSC defs env InDelay pats (apply f args) | ArgsList
       = concatMap (findSC defs env Unguarded pats) args

    -- If we're Guarded and find a Delay, continue with the argument as InDelay
    -- If we're Toplevel or Guarded and find a constructor, continue with the
    -- arguments as Guarded
    findSC defs env Guarded pats (apply (Ref (DataCon _ _) cn) args) | ArgsList
       = if isDelay cn defs
            then concatMap (findSC defs env InDelay pats) args
            else concatMap (findSC defs env Guarded pats) args
    findSC defs env Toplevel pats (apply (Ref (DataCon _ _) cn) args) | ArgsList
       = concatMap (findSC defs env Guarded pats) args

    -- If we find a function where all branches return a constructor (i.e.
    -- AllGuarded set) continue as Guarded (AllGuarded option is still TODO)
    -- If we find a function, calculate a size change as normal
    findSC defs env g pats (apply (Ref Func fn) args) | ArgsList 
       = let arity 
                = case lookupTyExact fn (gamma defs) of
                       Just ty => getArity defs [] ty
                       _ => 0 in
             findSCcall defs env Unguarded pats fn arity args
    -- Just look in the arguments, we already know 'f' isn't a function ref
    findSC defs env g pats (apply f args) | ArgsList 
       = concatMap (findSC defs env Unguarded pats) args

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
  smaller : Bool -> -- Have we gone under a constructor yet?
            Defs ->
            Maybe (Term vars) -> -- Asserted bigger thing
            Term vars -> -- Term we're checking
            Term vars -> -- Argument it might be smaller than
            Bool
  smaller inc defs big _ Erased = False -- Never smaller than an erased thing!
  smaller True defs big s t
      = if s == t
           then True
           else smallerArg True defs big s t
  smaller inc defs big s t = smallerArg inc defs big s t

  assertedSmaller : Maybe (Term vars) -> Term vars -> Bool
  assertedSmaller (Just b) a = b == a
  assertedSmaller _ _ = False

  smallerArg : Bool -> Defs ->
               Maybe (Term vars) -> Term vars -> Term vars -> Bool
  smallerArg inc defs big s tm
        -- If we hit a pattern that is equal to a thing we've asserted_smaller,
        -- the argument must be smaller
      = if assertedSmaller big tm
           then True
           else case getFnArgs tm of
                     (Ref (DataCon t a) cn, args) 
                         => if not (isDelay cn defs)
                               then any (smaller True defs big s) args
                               else False -- Can't be smaller than a delayed
                                          -- thing (which will be 'Infinite')
                                          -- since all others are erased
                     _ => case s of
                               App f _ => smaller inc defs big f tm 
                                            -- Higher order recursive argument
                               _ => False

  -- if the argument is an 'assert_smaller', return the thing it's smaller than,
  -- and the real argument
  asserted : Term vars -> Maybe (Term vars)
  asserted tm 
       = case getFnArgs tm of
              (Ref nt fn, [_, _, b, arg]) 
                   => if fn == NS ["Builtin"] (UN "assert_smaller")
                         then Just b
                         else Nothing
              _ => Nothing

  -- Calculate the size change for the given argument.
  -- i.e., return the size relationship of the given argument with an entry 
  -- in 'pats'; the position in 'pats' and the size change.
  -- Nothing if there is no relation with any of them.
  mkChange : Defs ->
             (pats : List (Nat, Term vars)) -> 
             (arg : Term vars) ->
             Maybe (Nat, SizeChange)
  mkChange defs [] arg = Nothing
  mkChange defs ((i, parg) :: pats) arg
      = cond [(arg == parg, Just (i, Same)),
              (smaller False defs (asserted arg) arg parg, Just (i, Smaller))]
          (mkChange defs pats arg)

  -- Given a name of a case function, and a list of the arguments being
  -- passed to it, return all the right hand sides as they match against those
  -- arguments.
  -- This way, we can build case blocks directly into the size change graph
  -- rather than treating the definitions separately.
  getCasePats : Defs -> Name -> List (Term vars) ->
                Maybe (List (Term vars))
  getCasePats {vars} defs n args
      = case lookupDefExact n (gamma defs) of
             Just (PMDef _ _ _ _ pdefs)
                => Just (map matchArgs pdefs)
             _ => Nothing
    where
      updateRHS : List (Term vs, Term vs') -> Term vs -> Term vs'
      updateRHS {vs} {vs'} ms tm
          = case lookup tm ms of
                 Nothing => urhs tm
                 Just t => t
        where
          urhs : Term vs -> Term vs'
          urhs (Local _ _) = Erased
          urhs (Ref nt f) = Ref nt f
          urhs (App f a) = App (updateRHS ms f) (updateRHS ms a)
          urhs (Bind x b sc)
              = Bind x (map (updateRHS ms) b) 
                  (updateRHS (map (\vt => (weaken (fst vt), weaken (snd vt))) ms) sc)
          urhs (PrimVal v) = PrimVal v
          urhs Erased = Erased
          urhs TType = TType

      matchArgs : (vs ** (Env Term vs, Term vs, Term vs)) -> Term vars
      matchArgs (_ ** (_, lhs, rhs))
         = let lhsMatch = zip (getArgs lhs) args in
               updateRHS lhsMatch rhs

  caseFn : Name -> Bool
  caseFn (GN (CaseBlock _ _)) = True
  caseFn (NS _ n) = caseFn n
  caseFn _ = False

  findSCcall : Defs -> Env Term vars -> Guardedness ->
               List (Nat, Term vars) ->
               Name -> Nat -> List (Term vars) ->
               List SCCall
  findSCcall defs env g pats fn arity args 
        -- Under 'assert_total' we assume that all calls are fine, so leave
        -- the size change list empty
      = cond [(fn == NS ["Builtin"] (UN "assert_total"), []),
              (caseFn fn, case getCasePats defs fn args of
                               Nothing => []
                               Just ps => concatMap (findSC defs env g pats) ps)]
             ([MkSCCall fn (expandToArity arity (map (mkChange defs pats) args))] 
                   ++ concatMap (findSC defs env g pats) args)

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
         findSC defs env Toplevel
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
-- TODO: If we encounter a name where we already know its termination status,
-- use that rather than continuing to traverse the graph!
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

-- Check whether a function is terminating, and record in the context
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

nameIn : Defs -> List Name -> NF [] -> Bool
nameIn defs tyns (NBind x b sc)
    = nameIn defs tyns (binderType b) ||
      nameIn defs tyns (sc (toClosure defaultOpts [] Erased))
nameIn defs tyns (NApp _ args)
    = any (nameIn defs tyns) (map (evalClosure defs) args)
nameIn defs tyns (NTCon n _ _ args)
    = if n `elem` tyns
         then True
         else any (nameIn defs tyns) (map (evalClosure defs) args)
nameIn defs tyns (NDCon n _ _ args)
    = any (nameIn defs tyns) (map (evalClosure defs) args)
nameIn defs tyns _ = False

-- Check an argument type doesn't contain a negative occurrence of any of
-- the given type names
posArg : Defs -> List Name -> NF [] -> Terminating
-- a tyn can only appear in the parameter positions of
-- tc; report positivity failure if it appears anywhere else
posArg defs tyns (NTCon tc _ _ args) 
    = let testargs : List (Closure [])
             = case lookupDefExact tc (gamma defs) of
                    Just (TCon _ _ _ params _ _) => dropParams 0 params args
                    _ => args in
          if any (nameIn defs tyns) (map (evalClosure defs) testargs)
             then NotTerminating NotStrictlyPositive
             else IsTerminating
  where
    dropParams : Nat -> List Nat -> List (Closure []) -> List (Closure [])
    dropParams i ps [] = []
    dropParams i ps (x :: xs)
        = if i `elem` ps
             then dropParams (S i) ps xs
             else x :: dropParams (S i) ps xs
-- a tyn can not appear as part of ty
posArg defs tyns (NBind x (Pi c e ty) sc) 
    = if nameIn defs tyns ty
         then NotTerminating NotStrictlyPositive
         else posArg defs tyns (sc (toClosure defaultOpts [] Erased))
posArg defs tyn _ = IsTerminating

checkPosArgs : Defs -> List Name -> NF [] -> Terminating
checkPosArgs defs tyns (NBind x (Pi c e ty) sc) 
    = case posArg defs tyns ty of
           IsTerminating => checkPosArgs defs tyns 
                                    (sc (toClosure defaultOpts [] Erased))
           bad => bad
checkPosArgs defs tyns _ = IsTerminating

checkCon : Defs -> List Name -> Name -> Terminating
checkCon defs tyns cn 
    = case lookupTyExact cn (gamma defs) of
           Nothing => Unchecked
           Just ty => checkPosArgs defs tyns (nf defs [] ty)

checkData : Defs -> List Name -> List Name -> Terminating
checkData defs tyns [] = IsTerminating
checkData defs tyns (c :: cs)
    = case checkCon defs tyns c of
           IsTerminating => checkData defs tyns cs
           bad => bad

-- Calculate whether a type satisfies the strict positivity condition, and
-- return whether it's terminating, along with its data constructors
calcPositive : {auto c : Ref Ctxt Defs} ->
               annot -> Name -> Core annot (Terminating, List Name)
calcPositive loc n 
    = do defs <- get Ctxt
         case lookupDefExact n (gamma defs) of
              Just (TCon _ _ tns _ _ dcons) => 
                  pure (checkData defs (n :: tns) dcons, dcons)
              Just _ => throw (GenericMsg loc (show n ++ " not a data type"))
              Nothing => throw (UndefinedName loc n)

-- Check whether a data type satisfies the strict positivity condition, and
-- record in the context
export
checkPositive : {auto c : Ref Ctxt Defs} ->
                annot -> Name -> Core annot Terminating
checkPositive loc n 
    = do tot <- getTotality loc n
         case isTerminating tot of
              Unchecked =>
                  do (tot', cons) <- calcPositive loc n
                     setTerminating loc n tot'
                     traverse (\c => setTerminating loc c tot') cons
                     pure tot'
              t => pure t

-- Check and record totality of the given name; positivity if it's a data
-- type, termination if it's a function                                                              
export
checkTotal : {auto c : Ref Ctxt Defs} ->
             annot -> Name -> Core annot Terminating
checkTotal loc n
    = do tot <- getTotality loc n
         defs <- get Ctxt
         case isTerminating tot of
              Unchecked =>
                  case lookupDefTyExact n (gamma defs) of
                       Just (TCon _ _ _ _ _ _, _)
                           => checkPositive loc n
                       _ => checkTerminating loc n
              t => pure t

