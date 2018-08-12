module Compiler.Inline

import Core.CompileExpr
import Core.Context
import Core.TT

import Data.List
import Data.Vect

%default covering

data EEnv : List Name -> List Name -> Type where
     Nil : EEnv free []
     (::) : CExp free -> EEnv free vars -> EEnv free (x :: vars)

weakenEnv : EEnv free vars -> EEnv (x :: free) vars
weakenEnv [] = []
weakenEnv (e :: env) = weaken e :: weakenEnv env

weakenNsEnv : (xs : List Name) -> EEnv free vars -> EEnv (xs ++ free) vars
weakenNsEnv [] env = env
weakenNsEnv (x :: xs) env = weakenEnv (weakenNsEnv xs env)

-- TODO: This is in CaseBuilder too, so tidy it up...
data LengthMatch : List a -> List b -> Type where
     NilMatch : LengthMatch [] []
     ConsMatch : LengthMatch xs ys -> LengthMatch (x :: xs) (y :: ys)

checkLengthMatch : (xs : List a) -> (ys : List b) -> Maybe (LengthMatch xs ys)
checkLengthMatch [] [] = Just NilMatch
checkLengthMatch [] (x :: xs) = Nothing
checkLengthMatch (x :: xs) [] = Nothing
checkLengthMatch (x :: xs) (y :: ys) 
    = Just (ConsMatch !(checkLengthMatch xs ys))

extend : EEnv free vars -> (args : List (CExp free)) -> (args' : List Name) ->
         LengthMatch args args' -> EEnv free (args' ++ vars)
extend env [] [] NilMatch = env
extend env (a :: xs) (n :: ns) (ConsMatch w) 
    = a :: extend env xs ns w

extendLoc : EEnv free vars -> (args' : List Name) -> EEnv (args' ++ free) (args' ++ vars)
extendLoc env [] = env
extendLoc env (n :: ns) = CLocal Here :: weakenEnv (extendLoc env ns)

Stack : List Name -> Type
Stack vars = List (CExp vars)
    
evalLocal : EEnv free vars -> Elem x (vars ++ free) ->
            CExp free
evalLocal {vars = []} env p = CLocal p
evalLocal {vars = x :: xs} (v :: env) Here = v
evalLocal {vars = x :: xs} (_ :: env) (There later) = evalLocal env later

unload : Stack vars -> CExp vars -> CExp vars
unload [] e = e
unload (a :: args) e = unload args (CApp e [a])

unloadApp : Nat -> Stack vars -> CExp vars -> CExp vars
unloadApp n args e = unload (drop n args) (CApp e (take n args))

getArity : CDef -> Nat
getArity (MkFun args _) = length args
getArity (MkCon _ arity) = arity
getArity (MkError _) = 0

takeFromStack : EEnv free vars -> Stack free -> (args : List Name) -> 
                Maybe (EEnv free (args ++ vars), Stack free)
takeFromStack env (e :: es) (a :: as) 
  = do (env', stk') <- takeFromStack env es as
       pure (e :: env', stk')
takeFromStack env stk [] = pure (env, stk)
takeFromStack env [] args = Nothing

thinAll : (ns : List Name) -> CExp (outer ++ inner) -> CExp (outer ++ ns ++ inner)
thinAll [] exp = exp
thinAll {outer} {inner} (n :: ns) exp 
    = thin {outer} {inner = ns ++ inner} n (thinAll ns exp)

parameters (defs : Defs)
  mutual
    tryApply : List Name -> Stack free -> EEnv free vars -> CDef -> Maybe (CExp free)
    tryApply {free} {vars} rec stk env (MkFun args exp)
        = do (env', stk') <- takeFromStack env stk args
             pure (eval rec env' stk' 
                     (rewrite sym (appendAssociative args vars free) in 
                              embed {vars = vars ++ free} exp))
    tryApply rec stk env _ = Nothing

    eval : List Name -> EEnv free vars -> Stack free -> CExp (vars ++ free) -> CExp free
    eval rec env stk (CLocal p) = unload stk $ evalLocal env p
    eval rec env stk (CRef n) 
        = case lookupGlobalExact n (gamma defs) of
               Nothing => unload stk (CRef n)
               Just gdef => 
                   case compexpr gdef of
                        Nothing => unload stk (CRef n)
                        Just def => 
                          let arity = getArity def in
                              if (Inline `elem` flags gdef) && (not (n `elem` rec))
                                 then maybe (unloadApp arity stk (CRef n)) id
                                            (tryApply (n :: rec) stk env def)
                                 else unloadApp arity stk (CRef n)
    eval {vars} {free} rec env [] (CLam x sc) 
        = let thinsc = thin x {outer = x :: vars} {inner = free} sc 
              sc' = eval rec (CLocal Here :: weakenEnv env) [] thinsc in
              CLam x sc'
    eval rec env (e :: stk) (CLam x sc) = eval rec (e :: env) stk sc
    eval {vars} {free} rec env stk (CLet x val sc) 
        = let thinsc = thin x {outer = x :: vars} {inner = free} sc 
              sc' = eval rec (CLocal Here :: weakenEnv env) [] thinsc in
              CLet x (eval rec env [] val) sc'
    eval rec env stk (CApp f args) 
        = eval rec env (map (eval rec env []) args ++ stk) f
    eval rec env stk (CCon n t args) = unload stk $ CCon n t (map (eval rec env []) args)
    eval rec env stk (COp p args) = unload stk $ COp p (map (eval rec env []) args)
    eval rec env stk (CExtPrim p args) = unload stk $ CExtPrim p (map (eval rec env []) args)
    eval rec env stk (CForce e)
        = case eval rec env [] e of
               CDelay e' => eval rec [] stk e'
               res => res
    eval rec env stk (CDelay e) = unload stk (CDelay (eval rec env [] e))
    eval rec env stk (CConCase sc alts def) 
        = let sc' = eval rec env [] sc in
              case pickAlt rec env stk sc' alts def of
                   Nothing => CConCase sc' (map (evalAlt rec env stk) alts)
                                           (map (eval rec env stk) def)
                   Just val => val
    eval rec env stk (CConstCase sc alts def) 
        = let sc' = eval rec env [] sc in
              case pickConstAlt rec env stk sc' alts def of
                   Nothing => CConstCase sc' (map (evalConstAlt rec env stk) alts)
                                             (map (eval rec env stk) def)
                   Just val => val
    eval rec env stk (CPrimVal c) = unload stk $ CPrimVal c
    eval rec env stk CErased = unload stk $ CErased
    eval rec env stk (CCrash str) = unload stk $ CCrash str

    evalAlt : List Name -> EEnv free vars -> Stack free -> CConAlt (vars ++ free) ->
              CConAlt free
    evalAlt {free} {vars} rec env stk (MkConAlt n t args sc) 
        = let sc' = thinAll {outer=args ++ vars} {inner=free} args 
                       (rewrite sym (appendAssociative args vars free) in sc)
              scEval = eval rec (extendLoc env args) (map (weakenNs args) stk) sc' in
              MkConAlt n t args scEval

    evalConstAlt : List Name -> EEnv free vars -> Stack free -> CConstAlt (vars ++ free) ->
                   CConstAlt free
    evalConstAlt rec env stk (MkConstAlt c sc)
        = MkConstAlt c (eval rec env stk sc)

    pickAlt : List Name -> EEnv free vars -> Stack free ->
              CExp free -> List (CConAlt (vars ++ free)) -> 
              Maybe (CExp (vars ++ free)) -> 
              Maybe (CExp free)
    pickAlt rec env stk (CCon n t args) [] def = map (eval rec env stk) def
    pickAlt {vars} {free} rec env stk (CCon n t args) (MkConAlt n' t' args' sc :: alts) def 
        = if t == t' 
             then case checkLengthMatch args args' of
                       Nothing => Nothing
                       Just m =>
                           let env' : EEnv free (args' ++ vars) 
                                  = extend env args args' m in
                               Just (eval rec env' stk 
                                      (rewrite sym (appendAssociative args' vars free) in 
                                               sc))
             else pickAlt rec env stk (CCon n t args) alts def
    pickAlt rec env stk _ _ _ = Nothing

    pickConstAlt : List Name -> EEnv free vars -> Stack free ->
                   CExp free -> List (CConstAlt (vars ++ free)) -> 
                   Maybe (CExp (vars ++ free)) -> 
                   Maybe (CExp free)
    pickConstAlt rec env stk (CPrimVal c) [] def = map (eval rec env stk) def
    pickConstAlt {vars} {free} rec env stk (CPrimVal c) (MkConstAlt c' sc :: alts) def 
        = if c == c' 
             then Just (eval rec env stk sc)
             else pickConstAlt rec env stk (CPrimVal c) alts def
    pickConstAlt rec env stk _ _ _ = Nothing

  inline : CDef -> CDef
  inline (MkFun args exp) = MkFun args (eval [] [] [] exp)
  inline d = d

export
inlineDef : {auto c : Ref Ctxt Defs} ->
            Name -> Core annot ()
inlineDef n
    = do defs <- get Ctxt
         case lookupGlobalExact n (gamma defs) of
              Nothing => pure ()
              Just def =>
                   case compexpr def of
                        Nothing => pure ()
                        Just cexpr =>
                             do -- coreLift $ putStrLn $ show n ++ " before: " ++ show cexpr
                                let inlined = inline defs cexpr
                                -- coreLift $ putStrLn $ show n ++ " after: " ++ show inlined
                                setCompiled n inlined
