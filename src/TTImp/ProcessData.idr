module TTImp.ProcessData

import Core.Context
import Core.Normalise
import Core.TT
import Core.Unify

import TTImp.Elab
import TTImp.TTImp

import Control.Catchable

checkCon : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST (UState annot)} ->
           {auto i : Ref ImpST (ImpState annot)} ->
           Elaborator annot -> 
           Env Term vars -> ImpTy annot ->
           Core annot Constructor
checkCon elab env (MkImpTy annot cn ty_raw)
    = do ty_imp <- mkBindImps ty_raw
         ty <- checkTerm elab env (PI False) InType ty_imp TType
         let ty' = abstractEnvType env ty
         -- TODO: Check 'ty' returns something in the right family
         gam <- getCtxt
         pure (MkCon cn (getArity gam [] ty') ty')

export
processData : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              Elaborator annot ->
              Env Term vars -> ImpData annot -> 
              Core annot ()
processData elab env (MkImpData annot n ty_raw cons_raw)
    = do ty_imp <- mkBindImps ty_raw
         ty <- checkTerm elab env (PI False) InType ty_imp TType
         -- TODO: Check ty returns a TType
         let ty' = abstractEnvType env ty
         addDef n (newDef ty' Public None)
         cons <- traverse (\x => checkCon elab env x) cons_raw
         gam <- getCtxt
         let def = MkData (MkCon n (getArity gam [] ty') ty') cons
         addData Public def

