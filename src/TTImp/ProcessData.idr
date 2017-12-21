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
           Env Term vars -> NestedNames vars -> ImpTy annot ->
           Core annot Constructor
checkCon elab env nest (MkImpTy annot cn_in ty_raw)
    = do cn <- inCurrentNS cn_in
         ty_imp <- mkBindImps env ty_raw
         ty <- checkTerm elab cn env nest (PI False) InType ty_imp TType
         let ty' = abstractEnvType env ty
         log 3 $ show cn ++ " : " ++ show ty'
         -- TODO: Check 'ty' returns something in the right family
         gam <- getCtxt
         pure (MkCon cn (getArity gam [] ty') ty')

export
processData : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              Elaborator annot ->
              Env Term vars -> NestedNames vars -> ImpData annot -> 
              Core annot ()
processData elab env nest (MkImpData annot n_in ty_raw cons_raw)
    = do n <- inCurrentNS n_in
         ty_imp <- mkBindImps env ty_raw
         ty <- checkTerm elab n env nest (PI False) InType ty_imp TType
         -- TODO: Check ty returns a TType
         let ty' = abstractEnvType env ty
         log 3 $ show n ++ " : " ++ show ty'
         gam <- getCtxt
         let arity = getArity gam [] ty'
         -- Add a temporary type constructor, to use while checking
         -- data constructors (tag is meaningless here, so just set to 0)
         addDef n (newDef ty' Public (TCon 0 arity [] []))
         cons <- traverse (\x => checkCon elab env nest x) cons_raw
         let def = MkData (MkCon n arity ty') cons
         addData Public def

