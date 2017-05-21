module Core.Typecheck

import Core.TT
import Core.Context
import Core.Evaluate
import Core.CaseTree

import Data.List

%default covering

-- All possible errors (not only typechecking errors)
public export
data Error = CantConvert (Env Term vars) (Term vars) (Term vars)
           | UndefinedName Name
           | NotFunctionType (Term vars)
           | Msg String

export
error : Error -> Either Error a
error = Left

export
doConvert : (Quote tm, Convert tm) => Gamma -> Env Term outer -> 
            tm outer -> tm outer -> Either Error ()
doConvert gam env x y 
    = if convert gam env x y 
         then pure ()
         else error (CantConvert env (quote env x) (quote env y))

parameters (gam : Gamma)
  mutual
    chk : Env Term vars -> Raw -> Either Error (Term vars, Term vars)
    chk env (RVar x) 
        = case defined x env of
               Nothing => 
                  case lookupDefTy x gam of
                       Just (PMDef _ _, ty) => 
                            pure $ (Ref Func x, embed ty)
                       Just (DCon tag arity, ty) => 
                            pure $ (Ref (DataCon tag arity) x, embed ty)
                       Just (TCon tag arity, ty) => 
                            pure $ (Ref (TyCon tag arity) x, embed ty)
                       Just (_, ty) => 
                            pure $ (Ref Func x, embed ty)
                       Nothing => error (UndefinedName x)
               Just loc => pure $ (Local loc, binderType (getBinder loc env))
    chk env (RBind nm b sc) 
        = do (b', bt) <- chkBinder env b
             (sc', sct) <- chk {vars = nm :: _} (b' :: env) sc
             pure $ discharge nm b' bt sc' sct
    chk env (RApp f a) 
        = do (f', fty) <- chk env f
             case whnf gam env fty of
                  VBind _ (Lam ty) sc => 
                        do (a', aty) <- chk env a
                           doConvert gam env ty (toClosure env aty)
                           let sc' = sc (toClosure env a')
                           pure (App f' a', quote env sc')
                  _ => error (NotFunctionType fty)
    chk env (RPrimVal x) = pure $ chkConstant x
    chk env RType = pure (TType, TType)

    chkBinder : Env Term vars -> Binder Raw -> 
                Either Error (Binder (Term vars), Term vars)
    chkBinder env (Lam ty) 
        = do (tyv, tyt) <- chk env ty
             doConvert gam env tyt TType
             pure (Lam tyv, tyt)
    chkBinder env (Let val ty) 
        = do (tyv, tyt) <- chk env ty
             (valv, valt) <- chk env val
             doConvert gam env tyv valt
             doConvert gam env tyt TType
             pure (Let valv tyv, tyt)
    chkBinder env (Pi x ty) 
        = do (tyv, tyt) <- chk env ty
             doConvert gam env tyt TType
             pure (Pi x tyv, tyt)
    chkBinder env (PVar ty) 
        = do (tyv, tyt) <- chk env ty
             doConvert gam env tyt TType
             pure (PVar tyv, tyt)
    chkBinder env (PVTy ty) 
        = do (tyv, tyt) <- chk env ty
             doConvert gam env tyt TType
             pure (PVTy tyv, tyt)

    discharge : (nm : Name) -> Binder (Term vars) -> Term vars ->
                Term (nm :: vars) -> Term (nm :: vars) -> 
                (Term vars, Term vars)
    discharge nm (Lam ty) bindty scope scopety 
         = (Bind nm (Lam ty) scope, Bind nm (Pi Explicit ty) scopety)
    discharge nm (Let val ty) bindty scope scopety 
         = (Bind nm (Let val ty) scope, Bind nm (Let val ty) scopety)
    discharge nm (Pi x ty) bindty scope scopety 
         = (Bind nm (Pi x ty) scope, bindty)
    discharge nm (PVar ty) bindty scope scopety 
         = (Bind nm (PVar ty) scope, Bind nm (PVTy ty) scopety)
    discharge nm (PVTy ty) bindty scope scopety 
         = (Bind nm (PVTy ty) scope, bindty)

    chkConstant : Constant -> (Term vars, Term vars)
    chkConstant (I x) = (PrimVal (I x), PrimVal IntType)
    chkConstant IntType = (PrimVal IntType, TType)
