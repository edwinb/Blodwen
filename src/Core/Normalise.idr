module Core.Normalise

import Core.CaseTree
import Core.Context
import Core.Primitives
import Core.TT

-- import Control.Monad.State
import Data.List
import Data.Vect

%default covering -- total is hard here, because the things we're evaluating
                  -- might not themselves terminate, but covering is important.

export
toClosure : Bool -> Env Term outer -> Term outer -> Closure outer
toClosure h env tm = MkClosure h [] env tm

-- Needs 'eval', defined later
export
evalClosure : Gamma -> Closure free -> NF free

%name LocalEnv loc, loc1
%name Closure thunk, thunk1

Stack : List Name -> Type
Stack vars = List (Closure vars)

parameters (gam : Gamma, holesonly : Bool)
  mutual
    eval : Env Term free -> LocalEnv free vars -> Stack free ->
           Term (vars ++ free) -> NF free
    eval env loc stk (Local p) = evalLocal env loc stk p
    eval env loc stk (Ref nt fn)
         = evalRef env loc stk nt fn
    eval env loc (closure :: stk) (Bind x (Lam _ ty) sc) 
         = eval env (closure :: loc) stk sc
    eval env loc stk (Bind x (Let val ty) sc) 
         = eval env (MkClosure holesonly loc env val :: loc) stk sc
    eval env loc stk (Bind x b sc) 
         = NBind x (map (eval env loc stk) b)
               (\arg => eval env (arg :: loc) stk sc)
    eval env loc stk (App fn arg) 
         = eval env loc (MkClosure holesonly loc env arg :: stk) fn
    eval env loc stk (PrimVal x) = NPrimVal x
    eval env loc stk Erased = NErased
    eval env loc stk TType = NType

    evalLocal : Env Term free -> LocalEnv free vars -> Stack free -> 
                Elem x (vars ++ free) -> NF free
    evalLocal {vars = []} env loc stk p 
        = case getBinder p env of
               Let val ty => eval env [] stk val
               b => NApp (NLocal p) stk
    evalLocal {vars = (x :: xs)} 
              env ((MkClosure _ loc' env' tm') :: locs) stk Here 
        = eval env' loc' stk tm'
    evalLocal {vars = (x :: xs)} env (_ :: loc) stk (There later) 
        = evalLocal env loc stk later

    evalOp : (Vect arity (NF free) -> Maybe (NF free)) ->
             NameType -> Name -> Stack free -> NF free
    evalOp {arity} fn nt n stk
        = case takeFromStack arity stk of
               -- Stack must be exactly the right height
               Just (args, []) => 
                  let argsnf = map (evalClosure gam) args in
                      case fn argsnf of
                           Nothing => NApp (NRef nt n) stk
                           Just res => res
               _ => NApp (NRef nt n) stk
                   

    evalRef : Env Term free -> LocalEnv free vars -> Stack free ->
              NameType -> Name -> NF free
    evalRef env loc stk nt fn
        = case lookupDefExact fn gam of
               Just (PMDef h args tree) =>
                 if h || not holesonly then
                    case extendFromStack args loc stk of
                         Nothing => NApp (NRef nt fn) stk
                         Just (loc', stk') => 
                              case evalTree env loc' stk' tree of
                                   Nothing => NApp (NRef nt fn) stk
                                   Just val => val
                    else NApp (NRef nt fn) stk
               Just (Builtin op) => evalOp (getOp op) nt fn stk
               Just (DCon tag arity _) => NDCon fn tag arity stk
               Just (TCon tag arity _ _) => NTCon fn tag arity stk
               _ => NApp (NRef nt fn) stk
    
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

    tryAlt : Env Term free ->
             LocalEnv free (more ++ vars) ->
             Stack free -> NF free -> CaseAlt more ->
             Maybe (NF free)
    tryAlt {more} {vars} env loc stk (NDCon nm tag' arity args') (ConCase x tag args sc) 
         = if tag == tag'
              then do bound <- getCaseBound args' args loc
                      let loc' : LocalEnv _ ((args ++ more) ++ vars) 
                          = rewrite sym (appendAssociative args more vars) in
                                    bound
                      evalTree env loc' stk sc
              else Nothing
    tryAlt env loc stk (NPrimVal c') (ConstCase c sc) 
         = if c == c' then evalTree env loc stk sc
                      else Nothing
    tryAlt env loc stk val (DefaultCase sc) = evalTree env loc stk sc
    tryAlt _ _ _ _ _ = Nothing


    findAlt : Env Term free ->
              LocalEnv free (args ++ vars) ->
              Stack free -> NF free -> List (CaseAlt args) ->
              Maybe (NF free)
    findAlt env loc stk val [] = Nothing
    findAlt env loc stk val (x :: xs) 
         = case tryAlt env loc stk val x of
                Nothing => findAlt env loc stk val xs
                Just x => Just x

    evalTree : Env Term free ->
               LocalEnv free (args ++ vars) -> Stack free -> 
               CaseTree args ->
               Maybe (NF free)
    evalTree {args} {vars} {free} env loc stk (Case x alts) 
      = let x' : List.Elem _ ((args ++ vars) ++ free) 
               = rewrite sym (appendAssociative args vars free) in
                         elemExtend x
            xval = evalLocal env loc [] x' in
                   findAlt env loc stk xval alts
    evalTree {args} {vars} {free} env loc stk (STerm tm) 
          = let tm' : Term ((args ++ vars) ++ free) 
                    = rewrite sym (appendAssociative args vars free) in
                              embed tm in
            Just (eval env loc stk tm')
    evalTree env loc stk (Unmatched msg) = Nothing
    evalTree env loc stk Impossible = Nothing
    
evalClosure gam (MkClosure h loc env tm)
    = eval gam h env loc [] tm
    

export
nf : Gamma -> Env Term free -> Term free -> NF free
nf gam env tm = eval gam False env [] [] tm

-- Only evaluate names which stand for solved holes
export
nfHoles : Gamma -> Env Term free -> Term free -> NF free
nfHoles gam env tm = eval gam True env [] [] tm

genName : IORef Int -> String -> IO Name
genName num root 
    = do n <- readIORef num
         writeIORef num (n + 1)
         pure (MN root n)

public export
interface Quote (tm : List Name -> Type) where
  quote : Gamma -> Env Term vars -> tm vars -> Term vars
  quoteGen : IORef Int ->
             Gamma -> Env Term vars -> tm vars -> IO (Term vars)

  -- Ugh. An STRef would be better (even if it would be implemented exactly
  -- like this, at least it would have an interface that prevented any chance
  -- of problems...)
  quote gam env tm 
      = unsafePerformIO (do num <- newIORef 0
                            quoteGen num gam env tm)
   
mutual
  quoteArgs : IORef Int -> Gamma -> Env Term free -> List (Closure free) -> 
              IO (List (Term free))
  quoteArgs num gam env [] = pure []
  quoteArgs num gam env (thunk :: args) 
        = pure $ !(quoteGen num gam env (evalClosure gam thunk)) :: 
                 !(quoteArgs num gam env args)

  quoteHead :  NHead free -> IO (Term free)
  quoteHead (NLocal y) = pure $ Local y
  quoteHead (NRef nt n) = pure $ Ref nt n

  quoteBinder : IORef Int -> Gamma -> Env Term free -> Binder (NF free) -> 
                IO (Binder (Term free))
  quoteBinder num gam env (Lam x ty) 
      = do ty' <- quoteGen num gam env ty
           pure (Lam x ty')
  quoteBinder num gam env (Let val ty) 
      = do val' <- quoteGen num gam env val
           ty' <- quoteGen num gam env ty
           pure (Let val' ty')
  quoteBinder num gam env (Pi x ty) 
      = do ty' <- quoteGen num gam env ty
           pure (Pi x ty')
  quoteBinder num gam env (PVar ty) 
      = do ty' <- quoteGen num gam env ty
           pure (PVar ty')
  quoteBinder num gam env (PLet val ty) 
      = do val' <- quoteGen num gam env val
           ty' <- quoteGen num gam env ty
           pure (PLet val' ty')
  quoteBinder num gam env (PVTy ty) 
      = do ty' <- quoteGen num gam env ty
           pure (PVTy ty')

  export
  Quote NF where
    quoteGen num gam env (NBind n b sc) 
        = do var <- genName num "qv"
             sc' <- quoteGen num gam env (sc (toClosure False env (Ref Bound var)))
             b' <- quoteBinder num gam env b
             pure (Bind n b' (refToLocal var n sc'))
    quoteGen num gam env (NApp f args) 
        = do f' <- quoteHead f
             args' <- quoteArgs num gam env args
             pure $ apply f' args'
    quoteGen num gam env (NDCon nm tag arity xs) 
        = do xs' <- quoteArgs num gam env xs
             pure $ apply (Ref (DataCon tag arity) nm) xs'
    quoteGen num gam env (NTCon nm tag arity xs) 
        = do xs' <- quoteArgs num gam env xs
             pure $ apply (Ref (TyCon tag arity) nm) xs'
    quoteGen num gam env (NPrimVal x) = pure $ PrimVal x
    quoteGen num gam env NErased = pure $ Erased
    quoteGen num gam env NType = pure $ TType

  export
  Quote Term where
    quoteGen num gam env tm = pure tm

export
Quote Closure where
  quoteGen num gam env thunk = quoteGen num gam env (evalClosure gam thunk)

export
normalise : Gamma -> Env Term free -> Term free -> Term free
normalise gam env tm = quote gam env (nf gam env tm)

export
normaliseHoles : Gamma -> Env Term free -> Term free -> Term free
normaliseHoles gam env tm = quote gam env (nfHoles gam env tm)

export
getValArity : Gamma -> Env Term vars -> NF vars -> Nat
getValArity gam env (NBind x (Pi _ _) sc) 
    = S (getValArity gam env (sc (MkClosure False [] env Erased)))
getValArity gam env val = 0

export
getArity : Gamma -> Env Term vars -> Term vars -> Nat
getArity gam env tm = getValArity gam env (nf gam env tm)

public export
interface Convert (tm : List Name -> Type) where
  convert : Gamma -> Env Term vars -> tm vars -> tm vars -> Bool
  convGen : IORef Int ->
            Gamma -> Env Term vars -> tm vars -> tm vars -> IO Bool

  -- Ugh. An STRef would be better (even if it would be implemented exactly
  -- like this, at least it would have an interface that prevented any chance
  -- of problems...)
  convert gam env tm tm' 
      = unsafePerformIO (do num <- newIORef 0
                            convGen num gam env tm tm')

mutual
  allConv : IORef Int -> Gamma -> Env Term vars ->
            List (Closure vars) -> List (Closure vars) -> IO Bool
  allConv num gam env [] [] = pure True
  allConv num gam env (x :: xs) (y :: ys) 
      = pure $ !(convGen num gam env x y) && !(allConv num gam env xs ys)
  allConv num gam env _ _ = pure False
  
  chkConvHead : Gamma -> Env Term vars ->
                NHead vars -> NHead vars -> IO Bool 
  chkConvHead gam env (NLocal x) (NLocal y) = pure $ sameVar x y
  chkConvHead gam env (NRef x y) (NRef x' y') = pure $ y == y'
  chkConvHead gam env x y = pure False

  export
  Convert NF where
    convGen num gam env (NBind x b scope) (NBind x' b' scope') 
        = do var <- genName num "convVar"
             let c = MkClosure False [] env (Ref Bound var)
             convGen num gam env (scope c) (scope' c)
    convGen num gam env tmx@(NBind x (Lam ix tx) scx) tmy
        = let etay = nf gam env (Bind x (Lam ix (quote empty env tx))
                                   (App (weaken (quote empty env tmy))
                                        (Local Here))) in
              convGen num gam env tmx etay
    convGen num gam env tmx tmy@(NBind y (Lam iy ty) scy)
        = let etax = nf gam env (Bind y (Lam iy (quote empty env ty))
                                   (App (weaken (quote empty env tmx))
                                        (Local Here))) in
              convGen num gam env etax tmy
    convGen num gam env (NApp val args) (NApp val' args') 
        = do hs <- chkConvHead gam env val val'
             as <- allConv num gam env args args'
             pure $ hs && as
    convGen num gam env (NDCon _ tag _ xs) (NDCon _ tag' _ xs') 
        = do as <- allConv num gam env xs xs'
             pure (tag == tag' && as)
    convGen num gam env (NTCon _ tag _ xs) (NTCon _ tag' _ xs')
        = do as <- allConv num gam env xs xs'
             pure (tag == tag' && as)
    convGen num gam env (NPrimVal x) (NPrimVal y) = pure (x == y)
    convGen num gam env NErased _ = pure True
    convGen num gam env _ NErased = pure True
    convGen num gam env NType NType = pure True
    convGen num gam env x y = pure False

  export
  Convert Term where
    convGen num gam env x y = convGen num gam env (nf gam env x) (nf gam env y)

  export
  Convert Closure where
    convGen num gam env thunkx thunky
        = convGen num gam env (evalClosure gam thunkx)
                              (evalClosure gam thunky)

