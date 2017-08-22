module Core.Normalise

import Core.TT
import Core.Context
import Core.CaseTree

import Control.Monad.State
import Data.List

%default covering -- total is hard here, because the things we're evaluating
                  -- might not themselves terminate, but covering is important.

mutual
  public export
  data LocalEnv : List Name -> List Name -> Type where
       Nil  : LocalEnv free []
       (::) : Closure free -> LocalEnv free vars -> LocalEnv free (x :: vars)

  public export
  data Closure : List Name -> Type where
       MkClosure : LocalEnv free vars -> 
                   Env Term free ->
                   Term (vars ++ free) -> Closure free

export
toClosure : Env Term outer -> Term outer -> Closure outer
toClosure env tm = MkClosure [] env tm

%name LocalEnv loc, loc1
%name Closure thunk, thunk1

-- Things you can apply arguments to
public export
data NHead : List Name -> Type where
     NLocal : Elem x vars -> NHead vars
     NRef   : NameType -> Name -> NHead vars

public export
data NF : List Name -> Type where
     NBind    : (x : Name) -> Binder (NF vars) ->
                (Closure vars -> NF vars) -> NF vars
     NApp     : NHead vars -> List (Closure vars) -> NF vars
     NDCon    : Name -> (tag : Int) -> (arity : Nat) -> 
                List (Closure vars) -> NF vars
     NTCon    : Name -> (tag : Int) -> (arity : Nat) -> 
                List (Closure vars) -> NF vars
     NPrimVal : Constant -> NF vars
     NErased  : NF vars
     NType    : NF vars

Stack : List Name -> Type
Stack vars = List (Closure vars)

parameters (gam : Gamma, holesonly : Bool)
  mutual
    eval : Env Term free -> LocalEnv free vars -> Stack free ->
           Term (vars ++ free) -> NF free
    eval env loc stk (Local p) = evalLocal env loc stk p
    eval env loc stk (Ref nt fn)
         = evalRef env loc stk nt fn
    eval env loc (closure :: stk) (Bind x (Lam ty) sc) 
         = eval env (closure :: loc) stk sc
    eval env loc stk (Bind x (Let val ty) sc) 
         = eval env (MkClosure loc env val :: loc) stk sc
    eval env loc stk (Bind x b sc) 
         = NBind x (map (eval env loc stk) b)
               (\arg => eval env (arg :: loc) stk sc)
    eval env loc stk (App fn arg) 
         = eval env loc (MkClosure loc env arg :: stk) fn
    eval env loc stk (PrimVal x) = NPrimVal x
    eval env loc stk Erased = NErased
    eval env loc stk TType = NType

    evalLocal : Env Term free -> LocalEnv free vars -> Stack free -> 
                Elem x (vars ++ free) -> NF free
    evalLocal {vars = []} env loc stk p 
        = case getBinder p env of
               Let val ty => eval env [] stk val
               b => NApp (NLocal p) []
    evalLocal {vars = (x :: xs)} 
              env ((MkClosure loc' env' tm') :: locs) stk Here 
        = eval env' loc' stk tm'
    evalLocal {vars = (x :: xs)} env (_ :: loc) stk (There later) 
        = evalLocal env loc stk later

    evalRef : Env Term free -> LocalEnv free vars -> Stack free ->
              NameType -> Name -> NF free
    evalRef env loc stk nt fn
        = case lookupDef fn gam of
               Just (PMDef h args tree) =>
                 if h || not holesonly then
                    case extendFromStack args loc stk of
                         Nothing => NApp (NRef nt fn) stk
                         Just (loc', stk') => 
                              case evalTree env loc' stk' tree of
                                   Nothing => 
                                        NApp (NRef nt fn) stk
                                   Just val => val
                    else NApp (NRef nt fn) stk
               Just (DCon tag arity) => 
                    case takeFromStack arity stk of
                         Nothing => NApp (NRef nt fn) stk
                         Just (args, stk') => 
                            NDCon fn tag arity (args ++ stk')
               Just (TCon tag arity _) =>
                    case takeFromStack arity stk of
                         Nothing => NApp (NRef nt fn) stk
                         Just (args, stk') => 
                            NTCon fn tag arity (args ++ stk')
               _ => NApp (NRef nt fn) stk
    
    -- Take arguments from the stack, as long as there's enough.
    -- Returns the arguments, and the rest of the stack
    takeFromStack : (arity : Nat) -> Stack free ->
                    Maybe (List (Closure free), Stack free)
    takeFromStack arity stk = takeStk arity stk []
      where
        takeStk : (remain : Nat) -> Stack free -> 
                  List (Closure free) -> 
                  Maybe (List (Closure free), Stack free)
        takeStk Z stk acc = Just (reverse acc, stk)
        takeStk (S k) [] acc = Nothing
        takeStk (S k) (arg :: stk) acc = takeStk k stk (arg :: acc)

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
                res => res

    evalTree : Env Term free ->
               LocalEnv free (args ++ vars) -> Stack free -> 
               CaseTree args ->
               Maybe (NF free)
    evalTree {args} {vars} {free} env loc stk (Case x alts) 
      = let x' : List.Elem _ ((args ++ vars) ++ free) 
               = rewrite sym (appendAssociative args vars free) in
                         elemExtend x
            xval = evalLocal env loc stk x' in
                   findAlt env loc stk xval alts
    evalTree {args} {vars} {free} env loc stk (STerm tm) 
          = let tm' : Term ((args ++ vars) ++ free) 
                    = rewrite sym (appendAssociative args vars free) in
                              embed tm in
            Just (eval env loc stk tm')
    evalTree env loc stk (Unmatched msg) = Nothing
    evalTree env loc stk Impossible = Nothing
    
export
evalClosure : Gamma -> Closure free -> NF free
evalClosure gam (MkClosure loc env tm)
    = eval gam False env loc [] tm
    

export
nf : Gamma -> Env Term free -> Term free -> NF free
nf gam env tm = eval gam False env [] [] tm

-- Only evaluate names which stand for solved holes
export
nfHoles : Gamma -> Env Term free -> Term free -> NF free
nfHoles gam env tm = eval gam True env [] [] tm

genName : String -> State Int Name
genName root 
    = do n <- get
         put (n + 1)
         pure (MN root n)

public export
interface Quote (tm : List Name -> Type) where
  quote : Gamma -> Env Term vars -> tm vars -> Term vars
  quoteGen :  Gamma -> Env Term vars -> tm vars -> State Int (Term vars)

  quote gam env tm = evalState (quoteGen gam env tm) 0
   
mutual
  quoteArgs : Gamma -> Env Term free -> List (Closure free) -> 
              State Int (List (Term free))
  quoteArgs gam env [] = pure []
  quoteArgs gam env (thunk :: args) 
        = pure $ !(quoteGen gam env (evalClosure gam thunk)) :: 
                 !(quoteArgs gam env args)

  quoteHead :  NHead free -> State Int (Term free)
  quoteHead (NLocal y) = pure $ Local y
  quoteHead (NRef nt n) = pure $ Ref nt n

  quoteBinder :  Gamma ->Env Term free -> Binder (NF free) -> 
                State Int (Binder (Term free))
  quoteBinder gam env (Lam ty) 
      = do ty' <- quoteGen gam env ty
           pure (Lam ty')
  quoteBinder gam env (Let val ty) 
      = do val' <- quoteGen gam env val
           ty' <- quoteGen gam env ty
           pure (Let val' ty')
  quoteBinder gam env (Pi x ty) 
      = do ty' <- quoteGen gam env ty
           pure (Pi x ty')
  quoteBinder gam env (PVar ty) 
      = do ty' <- quoteGen gam env ty
           pure (PVar ty')
  quoteBinder gam env (PVTy ty) 
      = do ty' <- quoteGen gam env ty
           pure (PVTy ty')

  export
  Quote NF where
    quoteGen gam env (NBind n b sc) 
        = do var <- genName "qv"
             sc' <- quoteGen gam env (sc (toClosure env (Ref Bound var)))
             b' <- quoteBinder gam env b
             pure (Bind n b' (refToLocal var n sc'))
    quoteGen gam env (NApp f args) 
        = do f' <- quoteHead f
             args' <- quoteArgs gam env args
             pure $ apply f' args'
    quoteGen gam env (NDCon nm tag arity xs) 
        = do xs' <- quoteArgs gam env xs
             pure $ apply (Ref (DataCon tag arity) nm) xs'
    quoteGen gam env (NTCon nm tag arity xs) 
        = do xs' <- quoteArgs gam env xs
             pure $ apply (Ref (TyCon tag arity) nm) xs'
    quoteGen gam env (NPrimVal x) = pure $ PrimVal x
    quoteGen gam env NErased = pure $ Erased
    quoteGen gam env NType = pure $ TType

  export
  Quote Term where
    quoteGen gam env tm = pure tm

export
Quote Closure where
  quoteGen gam env thunk = quoteGen gam env (evalClosure gam thunk)

export
normalise : Gamma -> Env Term free -> Term free -> Term free
normalise gam env tm = quote gam env (nf gam env tm)

export
normaliseHoles : Gamma -> Env Term free -> Term free -> Term free
normaliseHoles gam env tm = quote gam env (nfHoles gam env tm)

export
getValArity : Gamma -> Env Term vars -> NF vars -> Nat
getValArity gam env (NBind x (Pi _ _) sc) 
    = S (getValArity gam env (sc (MkClosure [] env Erased)))
getValArity gam env val = 0

export
getArity : Gamma -> Env Term vars -> Term vars -> Nat
getArity gam env tm = getValArity gam env (nf gam env tm)

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
  
  chkConvHead : Gamma -> Env Term vars ->
                NHead vars -> NHead vars -> State Int Bool 
  chkConvHead gam env (NLocal x) (NLocal y) = pure $ sameVar x y
  chkConvHead gam env (NRef x y) (NRef x' y') = pure $ y == y'
  chkConvHead gam env x y = pure False

  export
  Convert NF where
    convGen gam env (NBind x b scope) (NBind x' b' scope') 
        = do var <- genName "convVar"
             let c = MkClosure [] env (Ref Bound var)
             convGen gam env (scope c) (scope' c)
    convGen gam env (NApp val args) (NApp val' args') 
        = do hs <- chkConvHead gam env val val'
             as <- allConv gam env args args'
             pure $ hs && as
    convGen gam env (NDCon _ tag _ xs) (NDCon _ tag' _ xs') 
        = do as <- allConv gam env xs xs'
             pure (tag == tag' && as)
    convGen gam env (NTCon _ tag _ xs) (NTCon _ tag' _ xs')
        = do as <- allConv gam env xs xs'
             pure (tag == tag' && as)
    convGen gam env (NPrimVal x) (NPrimVal y) = pure (x == y)
    convGen gam env NErased _ = pure True
    convGen gam env _ NErased = pure True
    convGen gam env NType NType = pure True
    convGen gam env x y = pure False

  export
  Convert Term where
    convGen gam env x y = convGen gam env (nf gam env x) (nf gam env y)

  export
  Convert Closure where
    convGen gam env thunkx thunky
        = convGen gam env (evalClosure gam thunkx)
                          (evalClosure gam thunky)

