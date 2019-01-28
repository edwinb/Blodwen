module Core.Normalise

import Core.CaseTree
import Core.Context
import Core.Primitives
import Core.TT

-- import Control.Monad.State
import Data.List
import Data.Vect

import CompilerRuntime

%default covering -- total is hard here, because the things we're evaluating
                  -- might not themselves terminate, but covering is important.

export
toClosure : EvalOpts -> Env Term outer -> Term outer -> Closure outer
toClosure h env tm = MkClosure h [] env tm

-- Needs 'eval', defined later
export
evalClosure : Defs -> Closure free -> NF free

%name LocalEnv loc, loc1
%name Closure thunk, thunk1

Stack : List Name -> Type
Stack vars = List (Closure vars)

-- Use this to change the parameters in the block below. Needs to be forward
-- declared because it needs to be used within the block but has to be
-- defined outside it!
evalWithOpts : Defs -> EvalOpts ->
               Env Term free -> LocalEnv free vars -> Stack free ->
               Term (vars ++ free) -> NF free

parameters (defs : Defs, opts : EvalOpts)
  mutual
    eval : Env Term free -> LocalEnv free vars -> Stack free ->
           Term (vars ++ free) -> NF free
    eval env loc stk (Local r p) = evalLocal env loc stk r p
    eval env loc stk (Ref nt fn)
         = evalRef env loc stk nt fn
    eval env loc (closure :: stk) (Bind x (Lam _ _ ty) sc) 
         = eval env (closure :: loc) stk sc
    eval env loc stk (Bind x b@(Let n val ty) sc) 
         = if holesOnly opts
              then NBind x (map (eval env loc stk) b)
                      (\arg => eval env (arg :: loc) stk sc)
              else eval env (MkClosure opts loc env val :: loc) stk sc
    eval env loc stk (Bind x b sc) 
         = NBind x (map (eval env loc stk) b)
               (\arg => eval env (arg :: loc) stk sc)
    eval env loc stk (App fn arg) 
         = eval env loc (MkClosure opts loc env arg :: stk) fn
    eval env loc stk (PrimVal x) = NPrimVal x
    eval env loc stk Erased = NErased
    eval env loc stk TType = NType

    evalLocal : Env Term free -> 
                LocalEnv free vars -> Stack free -> 
                Maybe RigCount -> Elem x (vars ++ free) -> NF free
    evalLocal {vars = []} env loc stk r p 
        = if isLet p env && not (holesOnly opts)
             -- getBinder does a lot of work to weaken the types as
             -- necessary, so only do it if we really need to
             then case getBinder p env of
                       Let _ val ty => eval env [] stk val
                       b => NApp (NLocal r p) stk
             else NApp (NLocal r p) stk
      where
        isLet : Elem x vars -> Env tm vars -> Bool
        isLet Here (Let _ _ _ :: env) = True
        isLet Here _ = False
        isLet (There p) (b :: env) = isLet p env
    evalLocal {vars = (x :: xs)} 
              env ((MkClosure _ loc' env' tm') :: locs) stk r Here 
        = eval env' loc' stk tm'
    evalLocal {free} {vars = (x :: xs)} 
              env ((MkNFClosure nf) :: locs) stk r Here 
        = applyToStack nf stk
      where
        applyToStack : NF free -> Stack free -> NF free
        applyToStack (NBind _ (Lam r e ty) sc) (arg :: stk)
            = applyToStack (sc arg) stk
        applyToStack (NApp (NRef nt fn) args) stk
            = evalRef env locs (args ++ stk) nt fn
        applyToStack (NApp (NLocal r p) args) stk
            = evalLocal env locs (args ++ stk) r 
                  (insertElemNames {outer=[]} xs p)
        applyToStack (NDCon n t a args) stk = NDCon n t a (args ++ stk)
        applyToStack (NTCon n t a args) stk = NTCon n t a (args ++ stk)
        applyToStack nf _ = nf

    evalLocal {vars = (x :: xs)} env (_ :: loc) stk r (There later) 
        = evalLocal env loc stk r later

    evalOp : (Vect arity (NF free) -> Maybe (NF free)) ->
             NameType -> Name -> Stack free -> NF free
    evalOp {arity} fn nt n stk
        = case takeFromStack arity stk of
               -- Stack must be exactly the right height
               Just (args, []) => 
                  let argsnf = map (evalClosure defs) args in
                      case fn argsnf of
                           Nothing => NApp (NRef nt n) stk
                           Just res => res
               _ => NApp (NRef nt n) stk
                   
    evalDef : Env Term free -> LocalEnv free vars -> Stack free ->
              NameType -> Name -> List DefFlag -> Def -> NF free
    evalDef env loc stk nt fn flags (PMDef h args tree _ _)
        = if h || not (holesOnly opts) || 
                  (tcInline opts && elem TCInline flags) then
             case extendFromStack args loc stk of
                  Nothing => NApp (NRef nt fn) stk
                  Just (loc', stk') => 
                       evalTree env loc' stk' tree (NApp (NRef nt fn) stk)
             else NApp (NRef nt fn) stk
    -- Don't check 'holesOnly' here - effectively, this gives us constant
    -- folding f the stack happens to be appropriate
    evalDef env loc stk nt fn flags (Builtin op) = evalOp (getOp op) nt fn stk
    evalDef env loc stk nt fn flags (DCon tag arity _) = NDCon fn tag arity stk
    evalDef env loc stk nt fn flags (TCon tag arity _ _ _ _) = NTCon fn tag arity stk
    evalDef env loc stk nt fn flags _ = NApp (NRef nt fn) stk

    -- Only evaluate the name if its definition is visible in the current 
    -- namespace
    evalRef : Env Term free -> LocalEnv free vars -> Stack free ->
              NameType -> Name -> NF free
    evalRef env loc stk (DataCon tag arity) fn = NDCon fn tag arity stk
    evalRef env loc stk (TyCon tag arity) fn = NTCon fn tag arity stk
    evalRef env loc stk Bound fn = NApp (NRef Bound fn) stk
    evalRef env loc stk nt fn
        = case lookupGlobalExact fn (gamma defs) of
               Just def => 
                    if evalAll opts ||
                         reducibleIn (currentNS defs) fn (visibility def)
                       then evalDef env loc stk nt fn (flags def) (definition def)
                       else toRef (definition def) stk
               _ => NApp (NRef nt fn) stk
      where
        toRef : Def -> Stack free -> NF free
        toRef (DCon t a _) stk = NDCon fn t a stk
        toRef (TCon t a _ _ _ _) stk = NTCon fn t a stk
        toRef _ stk = NApp (NRef nt fn) stk

    -- Take arguments from the stack, as long as there's enough.
    -- Returns the arguments, and the rest of the stack
    takeFromStack : (arity : Nat) -> Stack free ->
                    Maybe (Vect arity (Closure free), Stack free)
    takeFromStack arity stk = takeStk arity stk []
      where
        takeStk : (remain : Nat) -> Stack free -> 
                  Vect got (Closure free) -> 
                  Maybe (Vect (got + remain) (Closure free), Stack free)
        takeStk {got} Z stk acc = Just (rewrite plusZeroRightNeutral got in
                                    reverse acc, stk)
        takeStk (S k) [] acc = Nothing
        takeStk {got} (S k) (arg :: stk) acc 
           = rewrite sym (plusSuccRightSucc got k) in
                     takeStk k stk (arg :: acc)

    extendFromStack : (args : List Name) -> 
                      LocalEnv free vars -> Stack free ->
                      Maybe (LocalEnv free (args ++ vars), Stack free)
    extendFromStack [] loc stk = Just (loc, stk)
    extendFromStack (n :: ns) loc [] = Nothing
    extendFromStack (n :: ns) loc (arg :: args) 
         = do (loc', stk') <- extendFromStack ns loc args
              pure (arg :: loc', stk')

    getCaseBound : List (Closure free) ->
                   (args : List Name) ->
                   LocalEnv free vars ->
                   Maybe (LocalEnv free (args ++ vars))
    getCaseBound [] [] loc = Just loc
    getCaseBound [] (x :: xs) loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) [] loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) (n :: ns) loc 
         = do loc' <- getCaseBound args ns loc
              pure (arg :: loc')

    evalConAlt : Env Term free -> 
                 LocalEnv free (more ++ vars) ->
                 Stack free -> 
                 (args : List Name) -> 
                 List (Closure free) -> 
                 CaseTree (args ++ more) ->
                 (default : NF free) -> 
                 NF free
    evalConAlt {more} {vars} env loc stk args args' sc def
         = maybe def (\bound => 
                            let loc' : LocalEnv _ ((args ++ more) ++ vars) 
                                = rewrite sym (appendAssociative args more vars) in
                                          bound in
                              evalTree env loc' stk sc def)
                     (getCaseBound args' args loc)

    tryAlt : Env Term free ->
             LocalEnv free (more ++ vars) ->
             Stack free -> NF free -> CaseAlt more ->
             (default : NF free) -> NF free
    -- Ordinary constructor matching
    tryAlt {more} {vars} env loc stk (NDCon nm tag' arity args') (ConCase x tag args sc) def
         = if tag == tag'
              then evalConAlt env loc stk args args' sc def
              else def
    -- Type constructor matching, in typecase
    tryAlt {more} {vars} env loc stk (NTCon nm tag' arity args') (ConCase nm' tag args sc) def
         = if nm == nm'
              then evalConAlt env loc stk args args' sc def
              else def
    -- Primitive type matching, in typecase
    tryAlt env loc stk (NPrimVal c) (ConCase (UN x) tag [] sc) def
         = if show c == x
              then evalTree env loc stk sc def
              else def
    -- Type of type matching, in typecase
    tryAlt env loc stk NType (ConCase (UN "Type") tag [] sc) def
         = evalTree env loc stk sc def
    -- Arrow matching, in typecase
    tryAlt {more} {vars}  
           env loc stk (NBind x (Pi r e aty) scty) (ConCase (UN "->") tag [s,t] sc) def
       = evalConAlt {more} {vars} env loc stk [s,t]
                  [MkNFClosure aty, 
                   MkNFClosure (NBind x (Lam r e aty) scty)]
                  sc def
    -- Constructor matching
    tryAlt env loc stk (NPrimVal c') (ConstCase c sc) def
         = if c == c' then evalTree env loc stk sc def
                      else def
    -- Default case matches against any *concrete* value
    tryAlt env loc stk val (DefaultCase sc) def
         = if concrete val 
              then evalTree env loc stk sc def
              else def
      where
        concrete : NF free -> Bool
        concrete (NDCon _ _ _ _) = True
        concrete (NTCon _ _ _ _) = True
        concrete (NPrimVal _) = True
        concrete (NBind _ _ _) = True
        concrete NType = True
        concrete _ = False
    tryAlt _ _ _ _ _ def = def


    findAlt : Env Term free ->
              LocalEnv free (args ++ vars) ->
              Stack free -> NF free -> List (CaseAlt args) ->
              (default : NF free) -> NF free
    findAlt env loc stk val [] def = def
    findAlt env loc stk val (x :: xs) def
         = tryAlt env loc stk val x (findAlt env loc stk val xs def)

    evalTree : Env Term free ->
               LocalEnv free (args ++ vars) -> Stack free -> 
               CaseTree args -> 
               (default : NF free) -> NF free
    evalTree {args} {vars} {free} env loc stk (Case x _ alts) def
      = let x' : List.Elem _ ((args ++ vars) ++ free) 
               = rewrite sym (appendAssociative args vars free) in
                         elemExtend x
            xval = evalLocal env loc [] Nothing x' in
                   findAlt env loc stk xval alts def
    evalTree {args} {vars} {free} env loc stk (STerm tm) def 
          = let tm' : Term ((args ++ vars) ++ free) 
                    = rewrite sym (appendAssociative args vars free) in
                              embed tm in
            case fuel opts of
                 Nothing => eval env loc stk tm'
                 Just Z => def
                 Just (S k) => 
                      let opts' = record { fuel = Just k } opts in
                          evalWithOpts defs opts' env loc stk tm'
    evalTree env loc stk (Unmatched msg) def = def
    evalTree env loc stk Impossible def = def
    
evalWithOpts = eval

evalClosure defs (MkClosure h loc env tm)
    = eval defs h env loc [] tm
evalClosure defs (MkNFClosure nf) = nf
    

export
nf : Defs -> Env Term free -> Term free -> NF free
nf defs env tm = eval defs defaultOpts env [] [] tm

export
nfOpts : EvalOpts -> Defs -> Env Term free -> Term free -> NF free
nfOpts opts defs env tm = eval defs opts env [] [] tm

-- Only evaluate names which stand for solved holes
export
nfHoles : Defs -> Env Term free -> Term free -> NF free
nfHoles defs env tm = eval defs withHoles env [] [] tm

-- Evaluate everything, even if not visible or not total (but work as
-- normal under binders and delay)
-- ('normalise' mode at the REPL)
export
nfAll : Defs -> Env Term free -> Term free -> NF free
nfAll defs env tm = eval defs withAll env [] [] tm

genName : BIORef Int -> String -> BIO Name
genName num root 
    = do n <- readIORef num
         writeIORef num (n + 1)
         pure (MN root n)

public export
interface Quote (tm : List Name -> Type) where
  quote : Defs -> Env Term vars -> tm vars -> Term vars
  quoteGen : BIORef Int ->
             Defs -> Env Term vars -> tm vars -> BIO (Term vars)

  -- Ugh. An STRef would be better (even if it would be implemented exactly
  -- like this, at least it would have an interface that prevented any chance
  -- of problems...)
  quote defs env tm 
      = unsafePerformIO (do num <- newIORef 0
                            quoteGen num defs env tm)
  
data Bounds : List Name -> Type where
     None : Bounds []
     Add : (x : Name) -> Name -> Bounds xs -> Bounds (x :: xs)

mutual
  quoteArgs : BIORef Int -> Defs -> Bounds bound ->
              Env Term free -> List (Closure free) -> 
              BIO (List (Term (bound ++ free)))
  quoteArgs num defs bound env [] = pure []
  quoteArgs num defs bound env (thunk :: args) 
        = pure $ !(quoteGenNF num defs bound env (evalClosure defs thunk)) :: 
                 !(quoteArgs num defs bound env args)

  quoteHead : Bounds bound -> NHead free -> BIO (Term (bound ++ free))
  quoteHead {bound} _ (NLocal r y) 
      = pure $ Local r (addThere bound y)
    where
      addThere : (ys : List Name) -> Elem x xs -> Elem x (ys ++ xs)
      addThere [] el = el
      addThere (x :: xs) el = There (addThere xs el)
  quoteHead bs (NRef Bound n) 
     = case findName bs of
            Just (_ ** p) => pure $ Local Nothing (elemExtend p)
            Nothing => pure $ Ref Bound n
    where
      findName : Bounds bound' -> Maybe (x ** Elem x bound')
      findName None = Nothing
      findName (Add x n' ns)
          = case nameEq n n' of
                 Just Refl => Just (_ ** Here)
                 Nothing => do (_ ** p) <- findName ns
                               Just (_ ** There p)
  quoteHead bound (NRef nt n) = pure $ Ref nt n

  quoteBinder : BIORef Int -> Defs -> Bounds bound ->
                Env Term free -> Binder (NF free) -> 
                BIO (Binder (Term (bound ++ free)))
  quoteBinder num defs bound env (Lam c x ty) 
      = do ty' <- quoteGenNF num defs bound env ty
           pure (Lam c x ty')
  quoteBinder num defs bound env (Let c val ty) 
      = do val' <- quoteGenNF num defs bound env val
           ty' <- quoteGenNF num defs bound env ty
           pure (Let c val' ty')
  quoteBinder num defs bound env (Pi c x ty) 
      = do ty' <- quoteGenNF num defs bound env ty
           pure (Pi c x ty')
  quoteBinder num defs bound env (PVar c ty) 
      = do ty' <- quoteGenNF num defs bound env ty
           pure (PVar c ty')
  quoteBinder num defs bound env (PLet c val ty) 
      = do val' <- quoteGenNF num defs bound env val
           ty' <- quoteGenNF num defs bound env ty
           pure (PLet c val' ty')
  quoteBinder num defs bound env (PVTy c ty) 
      = do ty' <- quoteGenNF num defs bound env ty
           pure (PVTy c ty')
  
  -- quoteGen, but also keeping track of the locals we introduced and
  -- need to resolve
  quoteGenNF : BIORef Int ->
               Defs -> Bounds bound -> 
               Env Term vars -> NF vars -> BIO (Term (bound ++ vars))
  quoteGenNF num defs bound env (NBind n b sc) 
      = do var <- genName num "qv"
           sc' <- quoteGenNF num defs (Add n var bound) env 
                       (sc (toClosure defaultOpts env (Ref Bound var)))
           b' <- quoteBinder num defs bound env b
           pure (Bind n b' sc') -- ?halp) -- (refToLocal Nothing var n sc'))
  quoteGenNF num defs bound env (NApp f args) 
      = do f' <- quoteHead bound f
           args' <- quoteArgs num defs bound env args
           pure $ apply f' args'
  quoteGenNF num defs bound env (NDCon nm tag arity xs) 
      = if isDelay nm defs
           then do xs' <- quoteArgs num defs bound env (map toHolesOnly xs)
                   pure $ apply (Ref (DataCon tag arity) nm) xs'
           else do xs' <- quoteArgs num defs bound env xs
                   pure $ apply (Ref (DataCon tag arity) nm) xs'
    where
      toHolesOnly : Closure vs -> Closure vs
      toHolesOnly (MkClosure _ locs env tm) = MkClosure withHoles locs env tm
      toHolesOnly c = c
  quoteGenNF num defs bound env (NTCon nm tag arity xs) 
      = do xs' <- quoteArgs num defs bound env xs
           pure $ apply (Ref (TyCon tag arity) nm) xs'
  quoteGenNF num defs bound env (NPrimVal x) = pure $ PrimVal x
  quoteGenNF num defs bound env NErased = pure $ Erased
  quoteGenNF num defs bound env NType = pure $ TType

  export
  Quote NF where
    quoteGen num defs env tm 
        = quoteGenNF num defs None env tm

  export
  Quote Term where
    quoteGen num defs env tm = pure tm

export
Quote Closure where
  quoteGen num defs env thunk = quoteGen num defs env (evalClosure defs thunk)

export
normalise : Defs -> Env Term free -> Term free -> Term free
normalise defs env tm = quote defs env (nf defs env tm)

export
normaliseOpts : EvalOpts -> Defs -> Env Term free -> Term free -> Term free
normaliseOpts opts defs env tm = quote defs env (nfOpts opts defs env tm)

export
normaliseHoles : Defs -> Env Term free -> Term free -> Term free
normaliseHoles defs env tm = quote defs env (nfHoles defs env tm)

export
normaliseAll : Defs -> Env Term free -> Term free -> Term free
normaliseAll defs env tm = quote defs env (nfAll defs env tm)

export
getValArity : Defs -> Env Term vars -> NF vars -> Nat
getValArity defs env (NBind x (Pi _ _ _) sc) 
    = S (getValArity defs env (sc (MkClosure defaultOpts [] env Erased)))
getValArity defs env val = 0

export
getArity : Defs -> Env Term vars -> Term vars -> Nat
getArity defs env tm = getValArity defs env (nf defs env tm)

public export
interface Convert (tm : List Name -> Type) where
  convert : Defs -> Env Term vars -> tm vars -> tm vars -> Bool
  convGen : BIORef Int ->
            Defs -> Env Term vars -> tm vars -> tm vars -> BIO Bool

  -- Ugh. An STRef would be better (even if it would be implemented exactly
  -- like this, at least it would have an interface that prevented any chance
  -- of problems...)
  convert defs env tm tm' 
      = unsafePerformIO (do num <- newIORef 0
                            convGen num defs env tm tm')

mutual
  allConv : BIORef Int -> Defs -> Env Term vars ->
            List (Closure vars) -> List (Closure vars) -> BIO Bool
  allConv num defs env [] [] = pure True
  allConv num defs env (x :: xs) (y :: ys) 
      = pure $ !(convGen num defs env x y) && !(allConv num defs env xs ys)
  allConv num defs env _ _ = pure False
  
  chkConvHead : Defs -> Env Term vars ->
                NHead vars -> NHead vars -> BIO Bool
  chkConvHead defs env (NLocal _ x) (NLocal _ y) = pure $ sameVar x y
  chkConvHead defs env (NRef x y) (NRef x' y') = pure $ y == y'
  chkConvHead defs env x y = pure False
  
  -- Comparing multiplicities when converting pi binders
  subRig : RigCount -> RigCount -> Bool
  subRig Rig1 RigW = True -- we can pass a linear function if a general one is expected
  subRig x y = x == y -- otherwise, the multiplicities need to match up

  convBinders : BIORef Int -> Defs -> Env Term vars ->
                Binder (NF vars) -> Binder (NF vars) -> BIO Bool
  convBinders num defs env (Pi cx ix tx) (Pi cy iy ty)
      = if ix /= iy || not (subRig cx cy)
           then pure False
           else convGen num defs env tx ty
  convBinders num defs env (Lam cx ix tx) (Lam cy iy ty)
      = if ix /= iy || cx /= cy
           then pure False
           else convGen num defs env tx ty
  convBinders num defs env bx by
      = if multiplicity bx /= multiplicity by
           then pure False
           else convGen num defs env (binderType bx) (binderType by)

  export
  Convert NF where
    convGen num defs env (NBind x b scope) (NBind x' b' scope') 
        = do var <- genName num "convVar"
             let c = MkClosure defaultOpts [] env (Ref Bound var)
             bok <- convBinders num defs env b b'
             if bok
                then convGen num defs env (scope c) (scope' c)
                else pure False
    convGen num defs env tmx@(NBind x (Lam c ix tx) scx) tmy
        = let etay = nf defs env (Bind x (Lam c ix (quote (noGam defs) env tx))
                                   (App (weaken (quote (noGam defs) env tmy))
                                        (Local Nothing Here))) in
              convGen num defs env tmx etay
    convGen num defs env tmx tmy@(NBind y (Lam c iy ty) scy)
        = let etax = nf defs env (Bind y (Lam c iy (quote (noGam defs) env ty))
                                   (App (weaken (quote (noGam defs) env tmx))
                                        (Local Nothing Here))) in
              convGen num defs env etax tmy
    convGen num defs env (NApp val args) (NApp val' args') 
        = do hs <- chkConvHead defs env val val'
             as <- allConv num defs env args args'
             pure $ hs && as
    convGen num defs env (NDCon nm tag _ xs) (NDCon nm' tag' _ xs') 
        = if isDelay nm defs || isDelay nm' defs
             then do as <- allConv num defs env (map toHolesOnly xs) (map toHolesOnly xs')
                     pure (tag == tag' && as)
             else do as <- allConv num defs env xs xs'
                     pure (tag == tag' && as)
      where
        toHolesOnly : Closure vs -> Closure vs
        toHolesOnly (MkClosure _ locs env tm) = MkClosure withHoles locs env tm
        toHolesOnly c = c
    convGen num defs env (NTCon name tag _ xs) (NTCon name' tag' _ xs')
        = do as <- allConv num defs env xs xs'
             -- Need to compare names rather than tags since tags may be
             -- reused in different namespaces!
             pure (name == name' && as)
    convGen num defs env (NPrimVal x) (NPrimVal y) = pure (x == y)
    convGen num defs env NErased _ = pure True
    convGen num defs env _ NErased = pure True
    convGen num defs env NType NType = pure True
    convGen num defs env x y = pure False

  export
  Convert Term where
    convGen num defs env x y 
        = if x == y 
             then pure True
             else convGen num defs env (nf defs env x) (nf defs env y)

  export
  Convert Closure where
    convGen num defs env thunkx thunky
        = convGen num defs env (evalClosure defs thunkx)
                               (evalClosure defs thunky)

replace' : Int -> Defs -> Env Term vars ->
           (lhs : NF vars) -> (parg : Term vars) -> (exp : NF vars) ->
           Term vars
replace' {vars} tmpi defs env lhs parg tm
    = if convert defs env lhs tm
         then parg
         else repSub tm
  where
    repSub : NF vars -> Term vars
    repSub (NBind x b scfn)
       = let b' = map repSub b 
             x' = MN "tmp" tmpi
             sc' = replace' (tmpi + 1) defs env lhs parg 
                            (scfn (toClosure defaultOpts env (Ref Bound x'))) in
             Bind x b' (refToLocal (Just (multiplicity b)) x' x sc')
    repSub (NApp hd []) = quote (noGam defs) env (NApp hd [])
    repSub (NApp hd args) 
       = apply (replace' tmpi defs env lhs parg (NApp hd []))
                (map (replace' tmpi defs env lhs parg) 
                     (map (evalClosure defs) args))
    repSub (NDCon n t a args)
       = apply (quote (noGam defs) env (NDCon n t a []))
                (map (replace' tmpi defs env lhs parg) 
                     (map (evalClosure defs) args))
    repSub (NTCon n t a args)
       = apply (quote (noGam defs) env (NTCon n t a []))
                (map (replace' tmpi defs env lhs parg) 
                     (map (evalClosure defs) args))
    repSub tm = quote (noGam defs) env tm

-- Replace any sub term which converts with 'orig' to 'new' in 'tm'.
-- Doesn't normalise the result
export
replace : Defs -> Env Term vars ->
          (orig : NF vars) -> (new : Term vars) -> (tm : NF vars) ->
          Term vars
replace = replace' 0
