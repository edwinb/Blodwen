module TTImp.ProcessType

import Core.TT
import Core.Unify
import Core.Context
import Core.Normalise
import Core.Reflect

import TTImp.Elab
import TTImp.TTImp
  
getRetTy : annot -> Defs -> NF [] -> Core annot Name
getRetTy loc ctxt (NBind x (Pi _ _ _) sc)
    = getRetTy loc ctxt (sc (MkClosure False [] [] Erased))
getRetTy loc ctxt (NTCon n _ _ _) = pure n
getRetTy loc ctxt tm 
    = throw (GenericMsg loc ("Can't use hints for return type "
               ++ show (quote (noGam ctxt) [] tm)))

processFnOpt : {auto c : Ref Ctxt Defs} ->
               annot -> Name -> FnOpt -> Core annot ()
processFnOpt loc ndef Inline 
    = setFlag loc ndef Inline
processFnOpt loc ndef Hint 
    = do ctxt <- get Ctxt
         case lookupTyExact ndef (gamma ctxt) of
              Nothing => throw (UndefinedName loc ndef)
              Just ty => do target <- getRetTy loc ctxt (nf ctxt [] ty)
                            addHintFor loc target ndef
processFnOpt loc ndef GlobalHint
    = addGlobalHint loc ndef

export
processType : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              {auto i : Ref ImpST (ImpState annot)} ->
              Reflect annot =>
              Elaborator annot ->
              Env Term vars -> NestedNames vars ->
              Visibility -> List FnOpt -> ImpTy annot -> 
              Core annot ()
processType elab env nest vis fnopts (MkImpTy loc n_in ty_raw)
    = do n <- inCurrentNS n_in

         -- Check 'n' is undefined
         gam <- get Ctxt
         case lookupDefTyExact n (gamma gam) of
              Just (_, _) => throw (AlreadyDefined loc n)
              Nothing => pure ()

         ty_imp <- mkBindImps env ty_raw
         ty <- wrapError (InType loc n) $
                  checkTerm elab n env nest (PI Rig0) InType ty_imp TType
         wrapError (InType loc n) $ checkUserHoles False

         log 1 $ show n ++ " : " ++ show (abstractFullEnvType env ty)

         checkNameVisibility loc n vis ty
         addDef n (newDef (abstractFullEnvType env ty) vis None)
         traverse (processFnOpt loc n) fnopts
         addToSave n

