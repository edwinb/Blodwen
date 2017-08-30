module TTImp.ProcessType

import Core.TT
import Core.Unify
import Core.Context

import TTImp.Elab
import TTImp.TTImp

import Control.Catchable
import Control.Monad.StateE

export
processType : Env Term vars ->
              ImpTy annot -> 
              Core annot [Ctxt ::: Defs, UST ::: UState annot,
                          ImpST ::: ImpState annot] ()
processType env (MkImpTy annot n ty_raw)
    = do ty_imp <- mkBindImps ty_raw
         ty <- checkTerm env (PI False) InType ty_imp TType
         -- putStrLn $ show n ++ " : " ++ show ty
         addDef n (newDef (abstractEnvType env ty) Public None)

