module Core.Evaluate

import Core.TT
import Core.Context
import Core.CaseTree

import Data.List
import Data.Vect

%default covering -- total is hard here...

mutual
  export
  data LocalEnv : List Name -> List Name -> Type where
       Nil  : LocalEnv outer []
       (::) : Closure outer -> LocalEnv outer scope -> LocalEnv outer (x :: scope)

  export
  data Closure : List Name -> Type where
       MkClosure : Env Term outer -> 
                   LocalEnv outer scope -> 
                   Term (scope ++ outer) -> Closure outer
     
public export
data Value : List Name -> Type where
     VLocal   : Elem x scope -> Value scope
     VBind    : (x : Name) -> Binder (Closure scope) -> 
                (Closure scope -> Closure scope) -> Value scope
     VApp     : Value scope -> Closure scope -> Value scope
     VPrimVal : Constant -> Value scope
     VRef     : NameType -> Name -> Value scope
                -- I think this might as well be Lists rather than Vect
     VDCon    : Name -> (tag : Int) -> Vect arity (Closure scope) -> Value scope
     VTCon    : Name -> (tag : Int) -> Vect arity (Closure scope) -> Value scope
     VType    : Value scope

Stack : List Name -> Type
Stack outer = List (Closure outer)

parameters (gam : Gamma)
  mutual
    evalLocal : Env Term outer ->
                LocalEnv outer scope -> Stack outer -> 
                Elem x (scope ++ outer) -> 
                Value outer
    evalLocal {scope = []} env loc stk p 
          = case getBinder p env of
                 Let val ty => eval env [] stk val
                 b => VLocal p
    evalLocal {scope = (x :: xs)} 
              env ((MkClosure env' loc' tm') :: locs) stk Here 
                   = eval env' loc' stk tm'
    evalLocal {scope = (x :: xs)} env (_ :: loc) stk (There later) 
                   = evalLocal env loc stk later

    -- Take arguments from the stack, as long as there's enough.
    -- Returns the arguments, and the rest of the stack
    takeFromStack : (arity : Nat) -> Stack outer ->
                    Maybe (Vect arity (Closure outer), Stack outer)
    takeFromStack arity stk = takeStk arity stk []
      where
        takeStk : (remain : Nat) -> Stack outer -> 
                  Vect got (Closure outer) -> 
                  Maybe (Vect (got + remain) (Closure outer), Stack outer)
        takeStk {got} Z stk vacc
            = rewrite plusZeroRightNeutral got in 
                      Just (reverse vacc, stk)
        takeStk (S k) [] vacc = Nothing
        takeStk {got} (S k) (arg :: stk) vacc 
            = rewrite sym (plusSuccRightSucc got k) in 
                      takeStk k stk (arg :: vacc)

    extendFromStack : (args : List Name) -> 
                      LocalEnv outer scope -> Stack outer ->
                      Maybe (LocalEnv outer (args ++ scope), Stack outer)
    extendFromStack [] loc stk = Just (loc, stk)
    extendFromStack (n :: ns) loc [] = Nothing
    extendFromStack (n :: ns) loc (arg :: args) 
         = do (loc', stk') <- extendFromStack ns loc args
              pure (arg :: loc', stk')

    getCaseBound : Vect arity (Closure outer) ->
                   (args : List Name) ->
                   LocalEnv outer scope ->
                   Maybe (LocalEnv outer (args ++ scope))
    getCaseBound [] [] loc = Just loc
    getCaseBound [] (x :: xs) loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) [] loc = Nothing -- mismatched arg length
    getCaseBound (arg :: args) (n :: ns) loc 
         = do loc' <- getCaseBound args ns loc
              pure (arg :: loc')

    tryAlt : Env Term outer ->
             LocalEnv outer (more ++ scope) ->
             Stack outer -> Value outer -> CaseAlt more ->
             Maybe (Value outer)
    tryAlt {more} {scope} env loc stk (VDCon nm tag' args') (ConCase x tag args sc) 
         = if tag == tag'
              then do bound <- getCaseBound args' args loc
                      let loc' : LocalEnv _ ((args ++ more) ++ scope) 
                          = rewrite sym (appendAssociative args more scope) in
                                    bound
                      evalTree env loc' stk sc
              else Nothing
    tryAlt env loc stk (VPrimVal c') (ConstCase c sc) 
         = if c == c' then evalTree env loc stk sc
                      else Nothing
    tryAlt env loc stk val (DefaultCase sc) = evalTree env loc stk sc
    tryAlt _ _ _ _ _ = Nothing

    findAlt : Env Term outer ->
              LocalEnv outer (args ++ scope) ->
              Stack outer -> Value outer -> List (CaseAlt args) ->
              Maybe (Value outer)
    findAlt env loc stk val [] = Nothing
    findAlt env loc stk val (x :: xs) 
         = case tryAlt env loc stk val x of
                Nothing => findAlt env loc stk val xs
                res => res

    evalTree : Env Term outer ->
               LocalEnv outer (args ++ scope) -> Stack outer -> 
               CaseTree args ->
               Maybe (Value outer)
    evalTree {args} {scope} {outer} env loc stk (Case x alts) 
      = let x' : List.Elem _ ((args ++ scope) ++ outer) 
               = rewrite sym (appendAssociative args scope outer) in
                         elemExtend x
            xval = evalLocal env loc stk x' in
                   findAlt env loc stk xval alts
    evalTree {args} {scope} {outer} env loc stk (STerm tm) 
          = let tm' : Term ((args ++ scope) ++ outer) 
                    = rewrite sym (appendAssociative args scope outer) in
                              embed tm in
            Just (eval env loc stk tm')
    evalTree env loc stk (Unmatched msg) = Nothing
    evalTree env loc stk Impossible = Nothing

    unload : Value outer -> Stack outer -> Value outer
    unload val [] = val
    unload val (arg :: xs) = unload (VApp val arg) xs

    eval : Env Term outer -> LocalEnv outer scope -> Stack outer -> 
           Term (scope ++ outer) -> Value outer
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
                         Just (args, stk') => unload (VDCon fn tag args) stk'
                Just (TCon tag arity) =>
                    case takeFromStack arity stk of
                         Nothing => unload (VRef nt fn) stk
                         Just (args, stk') => unload (VTCon fn tag args) stk'
                _ => unload (VRef nt fn) stk
    eval env loc (closure :: stk) (Bind x (Lam ty) tm) 
         = eval env (closure :: loc) stk tm

    eval env loc stk (Bind x b tm) 
         = unload (VBind x (map (MkClosure env loc) b)
                     (\arg => MkClosure env (arg :: loc) tm)) stk

    eval env loc stk (App fn arg) 
         = eval env loc (MkClosure env loc arg :: stk) fn
    eval env loc stk (PrimVal x) = unload (VPrimVal x) stk
    eval env loc stk TType = VType

export
whnf : Gamma -> Env Term outer -> Term outer -> Value outer
whnf gam env tm = eval gam env [] [] tm

parameters (gam : Gamma)
  mutual
    quoteArgs : Env Term outer -> Vect n (Closure outer) -> List (Term outer)
    quoteArgs env [] = []
    quoteArgs env (MkClosure env' loc' arg :: args) 
          = quote env (eval gam env' loc' [] arg) :: quoteArgs env args

    quote : Env Term outer -> Value outer -> Term outer
    quote env (VLocal y) = Local y
    quote env (VBind x b f) = ?quote_rhs_2
    quote env (VApp x y) = ?quote_rhs_3
    quote env (VPrimVal x) = PrimVal x
    quote env (VRef nt n) = Ref nt n
    quote env (VDCon nm tag {arity} xs) 
        = let xs' = quoteArgs env xs in
              apply (Ref (DataCon tag arity) nm) xs'
    quote env (VTCon nm tag xs) = ?quote_rhs_7
    quote env VType = TType

export
nf : Gamma -> Env Term outer -> Term outer -> Term outer
nf gam env tm = quote gam env (whnf gam env tm)
