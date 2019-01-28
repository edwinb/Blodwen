module Core.GetType

import Core.TT
import Core.Context
import Core.Normalise
import Core.CaseTree

import Data.List

%default covering
%hide Language.Reflection.Binder

-- Get the type of an already typechecked thing.
-- We need this (occasionally) because we don't store types in subterms (e.g. on
-- applications) and we don't keep the type of suterms up to date throughout 
-- unification. Perhaps we should? There's a trade off here, and recalculating on
-- the rare occasions it's necessary doesn't seem to cost too much, but keep an
-- eye on it...

parameters (loc : annot, gam : Defs)
  mutual
    chk : Env Term vars -> Term vars -> Either (Error annot) (Term vars)
    chk env (Local r p) 
        = pure $ binderType $ getBinder p env
    chk env (Ref nt n)
        = case lookupTyExact n (gamma gam) of
               Just ty => pure (embed ty)
               Nothing => Left (UndefinedName loc n)
    chk env (Bind nm b sc) 
        = do bt <- chkBinder env b
             sct <- chk {vars = nm :: _} (b :: env) sc
             pure $ discharge nm b bt sct
    chk env (App f a) 
        = do fty <- chk env f
             case nf gam env fty of
                  NBind _ (Pi _ _ ty) scdone => 
                        do aty <- chk env a
                           let sc' = scdone (toClosure defaultOpts env a)
                           pure (quote gam env sc')
                  _ => Left (NotFunctionType loc env fty)
    chk env (PrimVal x) = pure $ chkConstant x
    chk env TType = pure TType
    chk env Erased = pure Erased

    chkBinder : Env Term vars -> Binder (Term vars) -> 
                Either (Error annot) (Term vars)
    chkBinder env b = chk env (binderType b)

    discharge : (nm : Name) -> Binder (Term vars) ->
                Term vars -> Term (nm :: vars) -> (Term vars)
    discharge n (Lam c x ty) bindty scopety
        = Bind n (Pi c x ty) scopety
    discharge n (Let c val ty) bindty scopety
        = Bind n (Let c val ty) scopety
    discharge n (Pi c x ty) bindty scopety 
        = bindty
    discharge n (PVar c ty) bindty scopety 
        = Bind n (PVTy c ty) scopety
    discharge n (PLet c val ty) bindty scopety
        = Bind n (PLet c val ty) scopety
    discharge n (PVTy c ty) bindty scopety
        = bindty

    chkConstant : Constant -> Term vars
    chkConstant (I x) = PrimVal IntType
    chkConstant (BI x) = PrimVal IntegerType
    chkConstant (Str x) = PrimVal StringType
    chkConstant (Ch x) = PrimVal CharType
    chkConstant (Db x) = PrimVal DoubleType
    chkConstant WorldVal = PrimVal WorldType
    chkConstant _ = TType

export
getType : {auto c : Ref Ctxt Defs} ->
          annot -> Env Term vars ->
          (term : Term vars) -> Core annot (Term vars)
getType loc env term
    = case chk loc !(get Ctxt) env term of
           Left err => throw err
           Right ok => pure ok
