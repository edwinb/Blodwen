module TTImp.ProcessParams

import Core.TT
import Core.Unify
import Core.Context
import Core.Metadata
import Core.Normalise
import Core.Reflect

import TTImp.Elab
import TTImp.TTImp

%default covering
  
extend : Env Term extvs -> SubVars vs extvs ->
         NestedNames extvs ->
         Term extvs ->
         (vars' ** (SubVars vs vars', Env Term vars', NestedNames vars'))
extend env p nest (Bind n (Pi c e ty) sc)
    = extend (Pi c e ty :: env) (DropCons p) (weaken nest) sc
extend env p nest tm = (_ ** (p, env, nest))

export
processParams : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState annot)} ->
                {auto i : Ref ImpST (ImpState annot)} ->
                {auto m : Ref Meta (Metadata annot)} ->
                Reflect annot =>
                Elaborator annot ->
                Env Term vars -> NestedNames vars ->
                annot -> List (Name, RawImp annot) -> List (ImpDecl annot) ->
                Core annot ()
processParams {vars} {c} {u} {i} {m} elab env nest loc ps ds
    = do -- Turn the parameters into a function type, (x : ps) -> Type,
         -- then read off the environment from the elaborated type. This way
         -- we'll get all the implicit names we need
         let pty_raw = mkParamTy ps
         pty_imp <- mkBindImps env pty_raw
         log 10 $ "Checking " ++ show pty_imp
         (pty, _) <- checkTerm elab False (UN "[parameters]") env env SubRefl
                               nest (PI Rig0) InType
                               pty_imp TType
         let (vs ** (prf, env', nest')) = extend env SubRefl nest pty
         log 5 $ "New env: " ++ show env'

         -- Treat the names in the block as 'nested names' so that we expand
         -- the applications as we need to
         defNames <- traverse inCurrentNS (definedInBlock ds)
         let nestBlock = record { names $= ((map (applyEnv env') defNames) ++) } nest'
         traverse (elab c u i m False env' nestBlock) ds
         pure ()
  where
    mkParamTy : List (Name, RawImp annot) -> RawImp annot
    mkParamTy [] = IType loc
    mkParamTy ((n, ty) :: ps) 
       = IPi loc RigW Explicit (Just n) ty (mkParamTy ps)

    applyEnv : Env Term vs -> Name -> (Name, (Maybe Name, Term vs))
    applyEnv env n = (n, (Nothing, mkConstantAppFull n env))

