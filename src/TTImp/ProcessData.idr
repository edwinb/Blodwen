module TTImp.ProcessData

import Core.Context
import Core.Normalise
import Core.TT
import Core.Reflect
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

checkRetType : Env Term vars -> NF vars -> 
               (NF vars -> Core annot ()) -> Core annot ()
checkRetType env (NBind x (Pi _ _ ty) sc) chk
    = checkRetType env (sc (MkClosure False [] env Erased)) chk
checkRetType env nf chk = chk nf

checkIsType : annot -> Name -> Env Term vars -> NF vars -> Core annot ()
checkIsType loc n env nf
    = checkRetType env nf 
         (\nf => case nf of 
                      NType => pure ()
                      _ => throw (BadTypeConType loc n))

checkFamily : annot -> Name -> Name -> Env Term vars -> NF vars -> Core annot ()
checkFamily loc cn tn env nf
    = checkRetType env nf 
         (\nf => case nf of 
                      NType => pure ()
                      NTCon n' _ _ _ => 
                            if tn == n'
                               then pure ()
                               else throw (BadDataConType loc cn tn))

checkCon : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST (UState annot)} ->
           {auto i : Ref ImpST (ImpState annot)} ->
           Reflect annot =>
           Elaborator annot -> 
           Env Term vars -> NestedNames vars -> Visibility -> 
           Name -> ImpTy annot ->
           Core annot Constructor
checkCon elab env nest vis tn (MkImpTy loc cn_in ty_raw)
    = do cn <- inCurrentNS cn_in
         ty_imp <- mkBindImps env ty_raw
         ty <- wrapError (InCon loc cn) $
                  checkTerm elab cn env nest (PI Rig0) InType ty_imp TType
         wrapError (InCon loc cn) $ checkUserHoles loc False
         
         checkNameVisibility loc cn vis ty
         gam <- get Ctxt
         -- Check 'ty' returns something in the right family
         checkFamily loc cn tn env (nf gam env ty)

         let ty' = abstractEnvType env ty
         log 3 $ show cn ++ " : " ++ show ty'

         addToSave cn
         pure (MkCon cn (getArity gam [] ty') ty')

conName : Constructor -> Name
conName (MkCon cn _ _) = cn

export
processData : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              Reflect annot =>
              Elaborator annot ->
              Env Term vars -> NestedNames vars -> 
              Visibility -> ImpData annot -> 
              Core annot ()
processData elab env nest vis (MkImpLater loc n_in ty_raw)
    = do n <- inCurrentNS n_in
         ty_imp <- mkBindImps env ty_raw
         ty <- wrapError (InCon loc n) $
                  checkTerm elab n env nest (PI Rig0) InType ty_imp TType
         wrapError (InCon loc n) $ checkUserHoles loc False
         checkNameVisibility loc n vis ty

         gam <- get Ctxt
         -- Check 'n' is undefined
         case lookupDefTyExact n (gamma gam) of
              Just (_, _) => throw (AlreadyDefined loc n)
              Nothing => pure ()

         checkIsType loc n env (nf gam env ty)

         let ty' = abstractEnvType env ty
         log 3 $ show n ++ " : " ++ show ty'
         let arity = getArity gam [] ty'

         -- Add the type constructor as a placeholder
         addDef n (newDef ty' Public (TCon 0 arity [] [] []))

processData elab env nest vis (MkImpData loc n_in ty_raw dopts cons_raw)
    = do n <- inCurrentNS n_in
         ty_imp <- mkBindImps env ty_raw
         ty <- wrapError (InCon loc n) $
                  checkTerm elab n env nest (PI Rig0) InType ty_imp TType
         wrapError (InCon loc n) $ checkUserHoles loc False
         checkNameVisibility loc n vis ty

         gam <- get Ctxt
         checkIsType loc n env (nf gam env ty)

         let ty' = abstractEnvType env ty
         log 3 $ show n ++ " : " ++ show ty'
         let arity = getArity gam [] ty'

         -- If n exists, check it's the same type as we have here, and is
         -- a data constructor
         case lookupDefTyExact n (gamma gam) of
              Just (TCon _ _ [] [] [], ty_old) =>
                   if convert gam [] ty' ty_old
                      then pure ()
                      else throw (AlreadyDefined loc n)
              Just (_, _) => throw (AlreadyDefined loc n)
              Nothing => pure ()

         -- Add a temporary type constructor, to use while checking
         -- data constructors (tag is meaningless here, so just set to 0)
         addDef n (newDef ty' Public (TCon 0 arity [] [] []))
         
         -- Constructors are private if the data type as a whole is
         -- export
         let cvis = if vis == Export then Private else vis
         cons <- traverse (checkCon elab env nest cvis n) cons_raw

         -- Any non user defined holes should be resolved by now
         wrapError (InCon loc n) $ checkUserHoles loc True
         let def = MkData (MkCon n arity ty') cons
         addData vis def
        
         traverse (processDataOpt loc n) dopts
         when (not (NoHints `elem` dopts)) $
              do traverse (addHintFor loc n) (map conName cons)
                 pure ()
         addToSave n

