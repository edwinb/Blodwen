module Idris.Elab.Interface

import Core.Binary
import Core.Context
import Core.Core
import Core.TT
import Core.Unify

import Idris.BindImplicits
import Idris.Resugar
import Idris.Syntax

import TTImp.ProcessTTImp
import TTImp.Elab
import TTImp.Elab.Unelab
import TTImp.TTImp

mkDataTy : FC -> List (Name, RawImp FC) -> RawImp FC
mkDataTy fc [] = IType fc
mkDataTy fc ((n, ty) :: ps) 
    = IPi fc RigW Explicit (Just n) ty (mkDataTy fc ps)

mkIfaceData : FC -> Visibility -> Env Term vars ->
              List (Maybe Name, RawImp FC) ->
              Name -> List (Name, RawImp FC) -> List Name -> ImpDecl FC
mkIfaceData {vars} fc vis env constraints n ps dets
    = let opts = if isNil dets 
                    then [NoHints]
                    else [NoHints, SearchBy dets] in
          IData fc vis (MkImpData fc n 
                                  (bindTypeNames fc vars (mkDataTy fc ps)) 
                                  opts [])

-- Elaborate a method declaration so that we get all of its implicit
-- arguments in the right place, to be able to build the data declaration
getMethDecl : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState FC)} ->
              {auto i : Ref ImpST (ImpState FC)} ->
              Env Term vars -> NestedNames vars ->
              (params : List (Name, RawImp FC)) ->
              (FC, Name, RawImp FC) -> Core FC (Name, RawImp FC)
getMethDecl env nest params (fc, n, ty_raw)
    = do ty_imp <- mkBindImps env ty_raw
         let ty_params = bindParams params ty_imp
         ty <- wrapError (InType fc n) $
                 checkTerm (\c, u, i => processDecl {c} {u} {i})
                          n env nest (PI Rig0) InType ty_params TType
         pure (n, stripParams (map fst params) !(unelab fc env ty))
  where
    -- Implicitly bind the parameter names (they may appear only in function
    -- position in which case we don't automatically add them...)
    bindParams : List (Name, RawImp FC) -> RawImp FC -> RawImp FC
    bindParams [] ty = ty
    bindParams ((n, mty) :: ns) ty 
        = IPi fc Rig0 Implicit (Just n) mty (bindParams ns ty)
      
    -- We don't want the parameters to explicitly appear in the method
    -- type in the record for the interface (they are parameters of the
    -- interface type), so remove it here
    stripParams : List Name -> RawImp FC -> RawImp FC
    stripParams ps (IPi fc r p mn arg ret)
        = if (maybe False (\n => n `elem` ps) mn)
             then stripParams ps ret
             else IPi fc r p mn arg (stripParams ps ret)
    stripParams ps ty = ty

getSig : ImpDecl FC -> Maybe (FC, Name, RawImp FC)
getSig (IClaim _ _ _ (MkImpTy fc n ty)) = Just (fc, n, ty)
getSig _ = Nothing

export
elabInterface : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                {auto i : Ref ImpST (ImpState FC)} ->
                {auto s : Ref Syn SyntaxInfo} ->
                FC -> Visibility -> 
                Env Term vars -> NestedNames vars ->
                (constraints : List (Maybe Name, RawImp FC)) ->
                Name ->
                (params : List (Name, RawImp FC)) ->
                (dets : List Name) ->
                (conName : Maybe Name) ->
                List (ImpDecl FC) ->
                Core FC ()
elabInterface fc vis env nest constraints iname params dets conName body
    = do let dt = mkIfaceData fc vis env constraints iname params dets
         let meth_sigs = mapMaybe getSig body
         meths <- traverse (getMethDecl env nest params) meth_sigs
         log 0 $ "Methods: " ++ show meths
         log 0 $ "Made interface data type " ++ show dt
--          processDecls env nest [dt]
         throw (InternalError "Interfaces not done yet")

