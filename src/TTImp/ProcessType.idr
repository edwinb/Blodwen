module TTImp.ProcessType

import Core.TT
import Core.Unify
import Core.Context

import TTImp.Elab
import TTImp.TTImp

export
processType : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              Elaborator annot ->
              Env Term vars -> NestedNames vars ->
              ImpTy annot -> 
              Core annot ()
processType elab env nest (MkImpTy loc n_in ty_raw)
    = do n <- inCurrentNS n_in
         ty_imp <- mkBindImps env ty_raw
         ty <- wrapError (InType loc n) $
                  checkTerm elab n env nest (PI RigW) InType ty_imp TType
         wrapError (InType loc n) $ checkUserHoles loc False

         log 1 $ show n ++ " : " ++ show (abstractEnvType env ty)
         addDef n (newDef (abstractEnvType env ty) Public None)
         addToSave n

