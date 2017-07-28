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

parameters (gam : Gamma)
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

    evalClosure : Closure free -> NF free
    evalClosure (MkClosure loc env tm)
        = eval env loc [] tm
    
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
               Just (PMDef args tree) =>
                    case extendFromStack args loc stk of
                         Nothing => NApp (NRef nt fn) stk
                         Just (loc', stk') => 
                              case evalTree env loc' stk' tree of
                                   Nothing => 
                                        NApp (NRef nt fn) stk
                                   Just val => val
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
nf : Gamma -> Env Term free -> Term free -> NF free
nf gam env tm = eval gam env [] [] tm

genName : String -> State Int Name
genName root 
    = do n <- get
         put (n + 1)
         pure (MN root n)
   
parameters (gam : Gamma)
  mutual
    quoteArgs : Env Term free -> List (Closure free) -> 
                State Int (List (Term free))
    quoteArgs env [] = pure []
    quoteArgs env (thunk :: args) 
          = pure $ !(quoteGen env (evalClosure gam thunk)) :: 
                   !(quoteArgs env args)

    quoteHead : NHead free -> State Int (Term free)
    quoteHead (NLocal y) = pure $ Local y
    quoteHead (NRef nt n) = pure $ Ref nt n

    quoteBinder : Env Term free -> Binder (NF free) -> 
                  State Int (Binder (Term free))
    quoteBinder env (Lam ty) 
        = do ty' <- quoteGen env ty
             pure (Lam ty')
    quoteBinder env (Let val ty) 
        = do val' <- quoteGen env val
             ty' <- quoteGen env ty
             pure (Let val' ty')
    quoteBinder env (Pi x ty) 
        = do ty' <- quoteGen env ty
             pure (Pi x ty')
    quoteBinder env (PVar ty) 
        = do ty' <- quoteGen env ty
             pure (PVar ty')
    quoteBinder env (PVTy ty) 
        = do ty' <- quoteGen env ty
             pure (PVTy ty')

    quoteGen : Env Term free -> NF free -> State Int (Term free)
    quoteGen env (NBind n b sc) 
        = do var <- genName "qv"
             sc' <- quoteGen env (sc (toClosure env (Ref Bound var)))
             b' <- quoteBinder env b
             pure (Bind n b' (refToLocal var n sc'))
    quoteGen env (NApp f args) 
        = do f' <- quoteHead f
             args' <- quoteArgs env args
             pure $ apply f' args'
    quoteGen env (NDCon nm tag arity xs) 
        = do xs' <- quoteArgs env xs
             pure $ apply (Ref (DataCon tag arity) nm) xs'
    quoteGen env (NTCon nm tag arity xs) 
        = do xs' <- quoteArgs env xs
             pure $ apply (Ref (TyCon tag arity) nm) xs'
    quoteGen env (NPrimVal x) = pure $ PrimVal x
    quoteGen env NErased = pure $ Erased
    quoteGen env NType = pure $ TType

export
quote : Gamma -> Env Term free -> NF free -> Term free
quote gam env nf = evalState (quoteGen gam env nf) 0

export
normalise : Gamma -> Env Term free -> Term free -> Term free
normalise gam env tm = quote gam env (nf gam env tm)
