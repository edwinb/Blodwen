module Compiler.Inline

import Core.CompileExpr
import Core.Context
import Core.TT

import Data.List
import Data.Vect

data CVal : List Name -> Type where
     CSym : CVal vars
     CLet : CExp vars -> CVal vars

data EEnv : List Name -> Type where
     Nil : EEnv []
     (::) : CVal vars -> EEnv vars -> EEnv (x :: vars)

lookup : Elem x vars -> EEnv vars -> CExp vars
lookup Here (CSym :: env) = CLocal Here
lookup Here (CLet res :: env) = weaken res
lookup (There later) (e :: env) = weaken (lookup later env)

initEnv : (vars : List Name) -> EEnv vars
initEnv [] = []
initEnv (v :: vs) = CSym :: initEnv vs

parameters (defs : Defs)
  eval : EEnv vars -> CExp vars -> CExp vars
  eval env exp = exp

  inline : CDef -> CDef
  inline (MkFun args exp) = MkFun args (eval (initEnv args) exp)
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
                             do let inlined = inline defs cexpr
                                setCompiled n inlined
                                
