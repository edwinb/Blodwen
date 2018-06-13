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

-- TODO: Default method definitions
-- TODO: Check all the parts of the body are legal
-- TODO: Deal with default superclass implementations

mkDataTy : FC -> List (Name, RawImp FC) -> RawImp FC
mkDataTy fc [] = IType fc
mkDataTy fc ((n, ty) :: ps) 
    = IPi fc RigW Explicit (Just n) ty (mkDataTy fc ps)

mkIfaceData : FC -> Visibility -> Env Term vars ->
              List (Maybe Name, RawImp FC) ->
              Name -> Name -> List (Name, RawImp FC) -> 
              List Name -> List (Name, RawImp FC) -> ImpDecl FC
mkIfaceData {vars} fc vis env constraints n conName ps dets meths
    = let opts = if isNil dets 
                    then [NoHints]
                    else [NoHints, SearchBy dets] 
          retty = apply (IVar fc n) (map (IVar fc) (map fst ps))
          conty = mkTy Implicit Rig0 (map jname ps) $
                  mkTy Explicit RigW (constraints ++ map jname meths) retty
          con = MkImpTy fc conName (bindTypeNames fc vars conty) in
          IData fc vis (MkImpData fc n 
                                  (bindTypeNames fc vars (mkDataTy fc ps)) 
                                  opts [con])
  where
    jname : (Name, a) -> (Maybe Name, a)
    jname (n, t) = (Just n, t)

    mkTy : PiInfo -> RigCount ->
           List (Maybe Name, RawImp FC) -> RawImp FC -> RawImp FC
    mkTy imp c [] ret = ret
    mkTy imp c ((n, argty) :: args) ret
        = IPi fc c imp n argty (mkTy imp c args ret)

-- Get the implicit arguments for a method declaration, to allow us to build
-- the data declaration
getMethDecl : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState FC)} ->
              {auto i : Ref ImpST (ImpState FC)} ->
              Env Term vars -> NestedNames vars ->
              (params : List (Name, RawImp FC)) ->
              (FC, Name, RawImp FC) -> (Name, RawImp FC)
getMethDecl {vars} env nest params (fc, n, ty)
    = let ty_imp = bindTypeNames fc vars ty in
          (n, stripParams (map fst params) ty_imp)
  where
    -- We don't want the parameters to explicitly appear in the method
    -- type in the record for the interface (they are parameters of the
    -- interface type), so remove it here
    stripParams : List Name -> RawImp FC -> RawImp FC
    stripParams ps (IPi fc r p mn arg ret)
        = if (maybe False (\n => n `elem` ps) mn)
             then stripParams ps ret
             else IPi fc r p mn arg (stripParams ps ret)
    stripParams ps ty = ty

-- Get the top level function for implementing a method 
getMethToplevel : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST (UState FC)} ->
                  {auto i : Ref ImpST (ImpState FC)} ->
                  Env Term vars -> Visibility -> 
                  Name -> Name ->
                  (constraints : List (Maybe Name)) ->
                  (allmeths : List Name) ->
                  (params : List Name) ->
                  (FC, Name, RawImp FC) -> List (ImpDecl FC)
getMethToplevel {vars} env vis iname cname constraints allmeths params (fc, n, ty)
    = let ity = apply (IVar fc iname) (map (IVar fc) params) 
          ty_imp = bindTypeNames fc vars (bindIFace ity ty) 
          tydecl = IClaim fc vis [Inline] (MkImpTy fc n ty_imp) 
          conapp = apply (IVar fc cname)
                      (map (const (Implicit fc)) constraints ++
                       map (IBindVar fc) (map bindName allmeths))
          fnclause = PatClause fc (IImplicitApp fc (IVar fc n) (UN "__con")
                                                   conapp)
                                  (IVar fc (methName n)) 
          fndef = IDef fc n [fnclause] in
          [tydecl, fndef]
  where
    -- bind the auto implicit for the interface - put it after all the other
    -- implicits
    bindIFace : RawImp FC -> RawImp FC -> RawImp FC
    bindIFace ity (IPi fc rig Implicit n ty sc)
           = IPi fc rig Implicit n ty (bindIFace ity sc)
    bindIFace ity (IPi fc rig AutoImplicit n ty sc)
           = IPi fc rig AutoImplicit n ty (bindIFace ity sc)
    bindIFace ity sc = IPi fc RigW AutoImplicit (Just (UN "__con")) ity sc

    bindName : Name -> String
    bindName (UN n) = "__bind_" ++ n
    bindName (NS _ n) = bindName n
    bindName n = show n

    methName : Name -> Name
    methName n = UN (bindName n)

-- Get the function for chasing a constraint. This is one of the
-- arguments to the record, appearing before the method arguments.
getConstraintHint : {auto c : Ref Ctxt Defs} ->
                    {auto u : Ref UST (UState FC)} ->
                    {auto i : Ref ImpST (ImpState FC)} ->
                    FC -> Env Term vars -> Visibility -> 
                    Name -> Name ->
                    (constraints : List Name) ->
                    (allmeths : List Name) ->
                    (params : List Name) ->
                    (Name, RawImp FC) -> List (ImpDecl FC)
getConstraintHint {vars} fc env vis iname cname constraints meths params (cn, con)
    = let ity = apply (IVar fc iname) (map (IVar fc) params)
          fty = IPi fc RigW Explicit Nothing ity con
          ty_imp = bindTypeNames fc vars fty 
          hintname = MN ("__" ++ show iname ++ "_" ++ show con) 0
          tydecl = IClaim fc vis [Inline, Hint] (MkImpTy fc hintname ty_imp)
          conapp = apply (IVar fc cname)
                      (map (IBindVar fc) (map bindName constraints) ++
                       map (const (Implicit fc)) meths) 
          fnclause = PatClause fc (IApp fc (IVar fc hintname) conapp)
                                  (IVar fc (constName cn))
          fndef = IDef fc hintname [fnclause] in
          [tydecl, fndef]
  where
    bindName : Name -> String
    bindName (UN n) = "__bind_" ++ n
    bindName (NS _ n) = bindName n
    bindName n = show n

    constName : Name -> Name
    constName n = UN (bindName n)

getSig : ImpDecl FC -> Maybe (FC, Name, RawImp FC)
getSig (IClaim _ _ _ (MkImpTy fc n ty)) = Just (fc, n, ty)
getSig _ = Nothing

mkCon : Name -> Name
mkCon (NS ns (UN n)) = NS ns (MN ("__mk" ++ n) 0)
mkCon n = MN ("__mk" ++ show n) 0

-- Elaborate the data declaration part of the interface
export
elabAsData : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState FC)} ->
             {auto i : Ref ImpST (ImpState FC)} ->
             {auto s : Ref Syn SyntaxInfo} ->
             FC -> Visibility -> 
             Env Term vars -> NestedNames vars ->
             (constraints : List (Maybe Name, RawImp FC)) ->
             Name ->
             (params : List (Name, RawImp FC)) ->
             (dets : List Name) ->
             (conName : Name) ->
             List (FC, Name, RawImp FC) ->
             Core FC ()
elabAsData fc vis env nest constraints iname params dets conName meth_sigs
    = do let meths = map (getMethDecl env nest params) meth_sigs
         let dt = mkIfaceData fc vis env constraints iname conName params 
                              dets meths
         log 10 $ "Methods: " ++ show meths
         log 0 $ "Made interface data type " ++ show dt
         processDecls env nest [dt]

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
elabInterface fc vis env nest constraints iname params dets mcon body
    = do let conName_in = maybe (mkCon iname) id mcon
         -- Machine generated names need to be qualified when looking them up
         conName <- inCurrentNS conName_in
         let meth_sigs = mapMaybe getSig body
         elabAsData fc vis env nest constraints iname params dets conName meth_sigs

         -- Methods have same visibility as data declaration
         let fns = concatMap (getMethToplevel env vis iname conName
                                              (map fst constraints)
                                              (map (Basics.fst . Basics.snd) meth_sigs)
                                              (map fst params)) meth_sigs
         log 0 $ "Top level methods: " ++ show fns
         processDecls env nest fns

         let nconstraints = nameCons 0 constraints
         let chints = concatMap (getConstraintHint fc env vis iname conName
                                                   (map fst nconstraints)
                                                   (map (Basics.fst . Basics.snd) meth_sigs)
                                                   (map fst params)) nconstraints
         log 0 $ "Constraint hints from " ++ show constraints ++ ": " ++ show chints
         processDecls env nest chints
  where
    nameCons : Int -> List (Maybe Name, RawImp FC) -> List (Name, RawImp FC)
    nameCons i [] = []
    nameCons i ((_, ty) :: rest) 
        = (UN ("__con" ++ show i), ty) :: nameCons (i + 1) rest
