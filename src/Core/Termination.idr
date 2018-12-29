module Core.Termination

import Core.CaseTree
import Core.Context
import Core.Normalise
import Core.TT

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
findCalls defs (_ ** (env, lhs, rhs))
   = let pargs = getArgs (delazy defs lhs) in
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
