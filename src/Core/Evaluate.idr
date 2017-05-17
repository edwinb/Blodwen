module Core.Evaluate

import Core.TT
import Core.Context

import Data.List

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
Stack : List Name -> Type
Stack outer = List (Closure outer)

public export
data Value : List Name -> Type where
     VLocal   : Elem x scope -> Value scope
     VBind    : (x : Name) -> Binder (Closure scope) -> 
                (Closure scope -> Closure scope) -> Value scope
     VApp     : Value scope -> Closure scope -> Value scope
     VPrimVal : Constant -> Value scope
     VDCon    : (tag : Int) -> (arith : Int) -> Value scope
     VTCon    : (tag : Int) -> (arith : Int) -> Value scope
     VType    : Value scope

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

    unload : Value outer -> Stack outer -> Value outer
    unload val [] = val
    unload val (arg :: xs) = unload (VApp val arg) xs

    eval : Env Term outer -> LocalEnv outer scope -> Stack outer -> 
           Term (scope ++ outer) -> Value outer
    eval env loc stk (Local p) = evalLocal env loc stk p
    eval env loc stk (Ref x fn) = ?eval_rhs_2
    eval env loc (closure :: stk) (Bind x (Lam ty) tm) 
         = eval env (closure :: loc) stk tm

    eval env loc stk (Bind x b tm) 
         = unload (VBind x (map (MkClosure env loc) b)
                     (\arg => MkClosure env (arg :: loc) tm)) stk

    eval env loc stk (App fn arg) 
         = eval env loc (MkClosure env loc arg :: stk) fn
    eval env loc stk (PrimVal x) = unload (VPrimVal x) stk
    eval env loc stk TType = VType

