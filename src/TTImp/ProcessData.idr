module TTImp.ProcessData

import Core.Context
import Core.Normalise
import Core.TT
import Core.Unify

import TTImp.Elab
import TTImp.TTImp

import Control.Catchable
import Control.Monad.StateE

checkCon : Env Term vars -> ImpTy annot ->
           Core annot [Ctxt ::: Defs, UST ::: UState annot] Constructor
checkCon env (MkImpTy annot cn ty_raw)
    = do ty <- checkTerm env (PI False) ty_raw TType
         let ty' = abstractEnvType env ty
         -- TODO: Check 'ty' returns something in the right family
         gam <- getCtxt
         pure (MkCon cn (getArity gam [] ty') ty')

export
processData : Env Term vars -> ImpData annot -> 
              Core annot [Ctxt ::: Defs, UST ::: UState annot] ()
processData env (MkImpData annot n ty_raw cons_raw)
    = do ty <- checkTerm env (PI False) ty_raw TType
         -- TODO: Check ty returns a TType
         let ty' = abstractEnvType env ty
         addDef n (newDef ty' Public None)
         cons <- traverse (\x => checkCon env x) cons_raw
         gam <- getCtxt
         let def = MkData (MkCon n (getArity gam [] ty') ty') cons
         addData Public def

