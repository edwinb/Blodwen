module Core.Evaluate

import Core.TT
import Core.Context
import Core.CaseTree

import Control.Monad.State
import Data.List

%default covering -- total is hard here...

mutual
  export
  data LocalEnv : List Name -> List Name -> Type where
       Nil  : LocalEnv outer []
       (::) : Closure outer -> LocalEnv outer vars -> LocalEnv outer (x :: vars)

  export
  data Closure : List Name -> Type where
       MkClosure : LocalEnv outer vars -> 
                   Env Term outer ->
                   Term (vars ++ outer) -> Closure outer

%name LocalEnv loc, loc'
%name Closure thunk, thunk'

public export
data Value : List Name -> Type where
     VLocal   : Elem x vars -> Value vars
     VBind    : (x : Name) -> Binder (Closure vars) -> 
                (Closure vars -> Closure vars) -> Value vars
     VApp     : Value vars -> Closure vars -> Value vars
     VPrimVal : Constant -> Value vars
     VRef     : NameType -> Name -> Value vars
     VDCon    : Name -> (tag : Int) -> (arity : Nat) -> 
                List (Closure vars) -> Value vars
     VTCon    : Name -> (tag : Int) -> (arity : Nat) -> 
                List (Closure vars) -> Value vars
     VErased  : Value vars
     VType    : Value vars

%name Value val, val'

Stack : List Name -> Type
Stack outer = List (Closure outer)

parameters (gam : Gamma)
  mutual
    evalLocal : Env Term outer ->
                LocalEnv outer vars -> Stack outer -> 
                Elem x (vars ++ outer) -> 
                Value outer
    evalLocal {vars = []} env loc stk p 
          = case getBinder p env of
                 Let val ty => eval env [] stk val
                 b => VLocal p
    evalLocal {vars = (x :: xs)} 
              env ((MkClosure loc' env' tm') :: locs) stk Here 
                   = eval env' loc' stk tm'
    evalLocal {vars = (x :: xs)} env (_ :: loc) stk (There later) 
                   = evalLocal env loc stk later

    -- Take arguments from the stack, as long as there's enough.
    -- Returns the arguments, and the rest of the stack
    takeFromStack : (arity : Nat) -> Stack outer ->
                    Maybe (List (Closure outer), Stack outer)
    takeFromStack arity stk = takeStk arity stk []
      where
        takeStk : (remain : Nat) -> Stack outer -> 
                  List (Closure outer) -> 
                  Maybe (List (Closure outer), Stack outer)
        takeStk Z stk acc = Just (reverse acc, stk)
        takeStk (S k) [] acc = Nothing
        takeStk (S k) (arg :: stk) acc = takeStk k stk (arg :: acc)

    extendFromStack : (args : List Name) -> 
                      LocalEnv outer vars -> Stack outer ->
                      Maybe (LocalEnv outer (args ++ vars), Stack outer)
    extendFromStack [] loc stk = Just (loc, stk)
    extendFromStack (n :: ns) loc [] = Nothing
    extendFromStack (n :: ns) loc (arg :: args) 
         = do (loc', stk') <- extendFromStack ns loc args
              pure (arg :: loc', stk')

    getCaseBound : List (Closure outer) ->
                   (args : List Name) ->
                   LocalEnv outer vars ->
                   Maybe (LocalEnv outer (args ++ vars))
    getCaseBound [] [] loc = Just loc
    getCaseBound [] (x :: xs) loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) [] loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) (n :: ns) loc 
         = do loc' <- getCaseBound args ns loc
              pure (arg :: loc')

    tryAlt : Env Term outer ->
             LocalEnv outer (more ++ vars) ->
             Stack outer -> Value outer -> CaseAlt more ->
             Maybe (Value outer)
    tryAlt {more} {vars} env loc stk (VDCon nm tag' arity args') (ConCase x tag args sc) 
         = if tag == tag'
              then do bound <- getCaseBound args' args loc
                      let loc' : LocalEnv _ ((args ++ more) ++ vars) 
                          = rewrite sym (appendAssociative args more vars) in
                                    bound
                      evalTree env loc' stk sc
              else Nothing
    tryAlt env loc stk (VPrimVal c') (ConstCase c sc) 
         = if c == c' then evalTree env loc stk sc
                      else Nothing
    tryAlt env loc stk val (DefaultCase sc) = evalTree env loc stk sc
    tryAlt _ _ _ _ _ = Nothing

    findAlt : Env Term outer ->
              LocalEnv outer (args ++ vars) ->
              Stack outer -> Value outer -> List (CaseAlt args) ->
              Maybe (Value outer)
    findAlt env loc stk val [] = Nothing
    findAlt env loc stk val (x :: xs) 
         = case tryAlt env loc stk val x of
                Nothing => findAlt env loc stk val xs
                res => res

    evalTree : Env Term outer ->
               LocalEnv outer (args ++ vars) -> Stack outer -> 
               CaseTree args ->
               Maybe (Value outer)
    evalTree {args} {vars} {outer} env loc stk (Case x alts) 
      = let x' : List.Elem _ ((args ++ vars) ++ outer) 
               = rewrite sym (appendAssociative args vars outer) in
                         elemExtend x
            xval = evalLocal env loc stk x' in
                   findAlt env loc stk xval alts
    evalTree {args} {vars} {outer} env loc stk (STerm tm) 
          = let tm' : Term ((args ++ vars) ++ outer) 
                    = rewrite sym (appendAssociative args vars outer) in
                              embed tm in
            Just (eval env loc stk tm')
    evalTree env loc stk (Unmatched msg) = Nothing
    evalTree env loc stk Impossible = Nothing

    unload : Value outer -> Stack outer -> Value outer
    unload val [] = val
    unload val (arg :: xs) = unload (VApp val arg) xs

    eval : Env Term outer -> LocalEnv outer vars -> Stack outer -> 
           Term (vars ++ outer) -> Value outer
    eval env loc stk (Local p) = evalLocal env loc stk p
    eval env loc stk (Ref nt fn) 
         = case lookupDef fn gam of
                Just (PMDef args tree) => 
                    case extendFromStack args loc stk of
                         Nothing => unload (VRef nt fn) stk
                         Just (loc', stk') => 
                              case evalTree env loc' stk' tree of
                                   Nothing => unload (VRef nt fn) stk
                                   Just val => val
                Just (DCon tag arity) => 
                    case takeFromStack arity stk of
                         Nothing => unload (VRef nt fn) stk
                         Just (args, stk') => unload (VDCon fn tag arity args) stk'
                Just (TCon tag arity) =>
                    case takeFromStack arity stk of
                         Nothing => unload (VRef nt fn) stk
                         Just (args, stk') => unload (VTCon fn tag arity args) stk'
                _ => unload (VRef nt fn) stk
    eval env loc (closure :: stk) (Bind x (Lam ty) tm) 
         = eval env (closure :: loc) stk tm

    eval env loc stk (Bind x b tm) 
         = unload (VBind x (map (MkClosure loc env) b) 
                           (\arg => MkClosure (arg :: loc) env tm)) stk

    eval env loc stk (App fn arg) 
         = eval env loc (MkClosure loc env arg :: stk) fn
    eval env loc stk (PrimVal x) = unload (VPrimVal x) stk
    eval env loc stk Erased = VErased
    eval env loc stk TType = VType

export
whnf : Gamma -> Env Term outer -> Term outer -> Value outer
whnf gam env tm = eval gam env [] [] tm

export
evalClosure : Gamma -> Closure vars -> Value vars
evalClosure gam (MkClosure loc env tm) = eval gam env loc [] tm

export
normalise : Gamma -> Env Term outer -> Term outer -> Term outer
normalise gam env tm = quote env (whnf gam env tm)
  where 
   mutual
    quoteArgs : Env Term outer -> List (Closure outer) -> List (Term outer)
    quoteArgs env [] = []
    quoteArgs env (thunk :: args) 
          = quote env (evalClosure gam thunk) :: quoteArgs env args

    quoteClosure : Env Term outer -> Closure outer -> Term outer

    quote : Env Term outer -> Value outer -> Term outer
    quote env (VLocal y) = Local y
    quote env (VBind x b f) 
        = Bind x (map (quoteClosure env) b) ?quote_rhs_2
    quote env (VApp f (MkClosure loc env' arg)) 
        = ?quoteapp -- App (quote env f) (quote env (eval gam env' loc [] arg))
    quote env (VPrimVal x) = PrimVal x
    quote env (VRef nt n) = Ref nt n
    quote env (VDCon nm tag arity xs) 
        = let xs' = quoteArgs env xs in
              apply (Ref (DataCon tag arity) nm) xs'
    quote env (VTCon nm tag arity xs) 
        = let xs' = quoteArgs env xs in
              apply (Ref (TyCon tag arity) nm) xs'
    quote env VErased = Erased
    quote env VType = TType

public export
interface Convert (tm : List Name -> Type) where
  convert : Gamma -> Env Term vars -> tm vars -> tm vars -> Bool
  convGen : Gamma -> Env Term vars -> tm vars -> tm vars -> State Int Bool

  convert gam env tm tm' = evalState (convGen gam env tm tm') 0

mutual
  allConv : Gamma -> Env Term vars ->
            List (Closure vars) -> List (Closure vars) -> State Int Bool
  allConv gam env [] [] = pure True
  allConv gam env (x :: xs) (y :: ys) 
      = pure $ !(convGen gam env x y) && !(allConv gam env xs ys)
  allConv gam env _ _ = pure False

  genName : State Int Name
  genName = do n <- get
               put (n + 1)
               pure (MN "convVar" n)

  chkConv : Gamma -> Env Term vars -> 
            Value vars -> Value vars -> State Int Bool 
  chkConv gam env (VLocal x) (VLocal y) = pure $ sameVar x y
  chkConv gam env (VBind x b scope) (VBind x' b' scope') 
      = do var <- genName
           let c = MkClosure [] env (Ref Bound var)
           convGen gam env (scope c) (scope' c)
  chkConv gam env (VApp val arg) (VApp val' arg')
      = pure $ !(convGen gam env val val') && !(convGen gam env arg arg')
  chkConv gam env (VPrimVal x) (VPrimVal y) = pure $ x == y
  chkConv gam env (VRef x y) (VRef x' y') = pure $ y == y'
  chkConv gam env (VDCon _ tag _ xs) (VDCon _ tag' _ xs') 
      = pure $ (tag == tag' && !(allConv gam env xs xs'))
  chkConv gam env (VTCon _ tag _ xs) (VTCon _ tag' _ xs')
      = pure $ (tag == tag' && !(allConv gam env xs xs'))
  chkConv gam env VErased _ = pure True
  chkConv gam env _ VErased = pure True
  chkConv gam env VType VType = pure True
  chkConv gam env x y = pure False

  export
  Convert Value where
    convGen = chkConv

  export
  Convert Term where
    convGen gam env x y = convGen gam env (whnf gam env x) (whnf gam env y)

  Convert Closure where
    convGen gam env thunk thunk'
        = convGen gam env (evalClosure gam thunk)
                          (evalClosure gam thunk')

