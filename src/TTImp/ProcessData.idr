module TTImp.ProcessData

import Core.Context
import Core.Normalise
import Core.TT
import Core.Unify

import TTImp.Elab
import TTImp.TTImp

import Control.Catchable
  
  
processDataOpt : {auto c : Ref Ctxt Defs} ->
                 annot -> Name -> DataOpt -> Core annot ()
processDataOpt loc n NoHints 
    = pure ()
processDataOpt loc ndef (SearchBy dets) 
    = setDetermining loc ndef dets
  
checkCon : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST (UState annot)} ->
           {auto i : Ref ImpST (ImpState annot)} ->
           Elaborator annot -> 
           Env Term vars -> NestedNames vars -> Visibility -> ImpTy annot ->
           Core annot Constructor
checkCon elab env nest vis (MkImpTy loc cn_in ty_raw)
    = do cn <- inCurrentNS cn_in
         ty_imp <- mkBindImps env ty_raw
         ty <- wrapError (InCon loc cn) $
                  checkTerm elab cn env nest (PI RigW) InType ty_imp TType
         wrapError (InCon loc cn) $ checkUserHoles loc False
         
         checkNameVisibility loc cn vis ty

         let ty' = abstractEnvType env ty
         log 3 $ show cn ++ " : " ++ show ty'
         -- TODO: Check 'ty' returns something in the right family
         gam <- get Ctxt
         addToSave cn
         pure (MkCon cn (getArity gam [] ty') ty')

conName : Constructor -> Name
conName (MkCon cn _ _) = cn

export
processData : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              Elaborator annot ->
              Env Term vars -> NestedNames vars -> 
              Visibility -> ImpData annot -> 
              Core annot ()
processData elab env nest vis (MkImpData loc n_in ty_raw dopts cons_raw)
    = do n <- inCurrentNS n_in
         ty_imp <- mkBindImps env ty_raw
         ty <- wrapError (InCon loc n) $
                  checkTerm elab n env nest (PI RigW) InType ty_imp TType
         wrapError (InCon loc n) $ checkUserHoles loc False
           
         checkNameVisibility loc n vis ty

         -- TODO: Check ty returns a TType
         let ty' = abstractEnvType env ty
         log 3 $ show n ++ " : " ++ show ty'
         gam <- get Ctxt
         let arity = getArity gam [] ty'
         -- Add a temporary type constructor, to use while checking
         -- data constructors (tag is meaningless here, so just set to 0)
         addDef n (newDef ty' Public (TCon 0 arity [] [] []))
         
         -- Constructors are private if the data type as a whole is
         -- export
         let cvis = if vis == Export then Private else vis
         cons <- traverse (checkCon elab env nest cvis) cons_raw

         -- Any non user defined holes should be resolved by now
         wrapError (InCon loc n) $ checkUserHoles loc True
         let def = MkData (MkCon n arity ty') cons
         addData vis def
        
         traverse (processDataOpt loc n) dopts
         when (not (NoHints `elem` dopts)) $
              do traverse (addHintFor loc n) (map conName cons)
                 pure ()
         addToSave n

