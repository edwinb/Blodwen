module Idris.Elab.Interface

import Core.Binary
import Core.Context
import Core.Core
import Core.TT
import Core.Unify

import Idris.BindImplicits
import Idris.Syntax

import TTImp.ProcessTTImp
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
                                  (bindNames True vars (mkDataTy fc ps)) 
                                  opts [])

export
elabInterface : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                FC -> Visibility -> 
                Env Term vars -> NestedNames vars ->
                (constraints : List (Maybe Name, RawImp FC)) ->
                Name ->
                (params : List (Name, RawImp FC)) ->
                (det : List Name) ->
                (conName : Maybe Name) ->
                List (ImpDecl FC) ->
                Core FC ()
elabInterface fc vis env nest constraints iname params dets conName body
    = do let dt = mkIfaceData fc vis env constraints iname params dets
         log 0 $ "Made interface data type " ++ show dt
--          processDecls env nest [dt]
         throw (InternalError "Interfaces not done yet")

