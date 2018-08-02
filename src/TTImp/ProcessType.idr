module TTImp.ProcessType

import Core.TT
import Core.Unify
import Core.Context
import Core.Normalise
import Core.Reflect

import TTImp.Elab
import TTImp.TTImp

%default covering
  
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
processFnOpt loc ndef (Hint d)
    = do ctxt <- get Ctxt
         case lookupTyExact ndef (gamma ctxt) of
              Nothing => throw (UndefinedName loc ndef)
              Just ty => do target <- getRetTy loc ctxt (nf ctxt [] ty)
                            addHintFor loc target ndef d
processFnOpt loc ndef (GlobalHint a)
    = addGlobalHint loc a ndef
processFnOpt loc ndef ExternFn
    = pure ()

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
         log 5 $ "Checking type decl " ++ show n ++ " : " ++ show ty_raw

         -- Check 'n' is undefined
         gam <- get Ctxt
         case lookupDefTyExact n (gamma gam) of
              Just (_, _) => throw (AlreadyDefined loc n)
              Nothing => pure ()

         ty_imp <- mkBindImps env ty_raw
         (ty, _) <- wrapError (InType loc n) $
                      checkTerm elab n env nest (PI Rig0) InType ty_imp TType

         log 1 $ show n ++ " : " ++ show (abstractFullEnvType env ty)

         checkNameVisibility loc n vis ty
         -- If it's declared as externally defined, set the definition to
         -- ExternFn <arity>, where the arity is assumed to be fixed (i.e.
         -- not dependent on any of the arguments)
         let def = if ExternFn `elem` fnopts
                      then ExternDef (getArity gam env ty)
                      else None
         addDef n (newDef (abstractFullEnvType env ty) vis def)

         traverse (processFnOpt loc n) fnopts
         addToSave n

