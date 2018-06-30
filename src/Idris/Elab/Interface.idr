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
                  mkTy Explicit RigW (constraints ++ map bname meths) retty
          con = MkImpTy fc conName (bindTypeNames (map fst ps ++ vars) conty) in
          IData fc vis (MkImpData fc n 
                                  (bindTypeNames (map fst ps ++ vars)
                                                 (mkDataTy fc ps)) 
                                  opts [con])
  where
    jname : (Name, RawImp FC) -> (Maybe Name, RawImp FC)
    jname (n, t) = (Just n, t)

    bname : (Name, RawImp FC) -> (Maybe Name, RawImp FC)
    bname (n, t) = (Just n, IBindHere (getAnnot t) t)

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
    = let ty_imp = bindTypeNames (map fst params ++ vars) ty in
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
          ty_imp = bindTypeNames vars (bindIFace ity ty) 
          tydecl = IClaim fc vis [Inline] (MkImpTy fc n ty_imp) 
          conapp = apply (IVar fc cname)
                      (map (const (Implicit fc)) constraints ++
                       map (IBindVar fc) (map bindName allmeths))
          fnclause = PatClause fc (IImplicitApp fc (IVar fc n) 
                                                   (Just (MN "__con" 0))
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
    bindIFace ity sc = IPi fc RigW AutoImplicit (Just (MN "__con" 0)) ity sc

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
          ty_imp = bindTypeNames vars fty 
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

updateIfaceSyn : {auto s : Ref Syn SyntaxInfo} ->
                 Name -> Name -> List Name -> 
                 List (Name, RawImp FC) -> List (Name, ImpDecl FC) ->
                 Core FC ()
updateIfaceSyn iname cn ps ms ds
    = do syn <- get Syn
         let info = MkIFaceInfo cn ps ms ds
         put Syn (record { ifaces $= addCtxt iname info } syn)

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
         let meth_sigs = mapMaybe getSig body -- (FC, Name, RawImp FC)
         let meth_decls = map snd meth_sigs -- (Name, RawIMp FC)
         let meth_names = map fst meth_decls

         elabAsData conName meth_sigs
         elabMethods conName meth_names meth_sigs
         elabConstraintHints conName meth_names

         ns_meths <- traverse (\mt => do n <- inCurrentNS (fst mt)
                                         pure (n, snd mt)) meth_decls
         ns_iname <- inCurrentNS iname
         updateIfaceSyn ns_iname conName (map fst params) ns_meths []
  where
    nameCons : Int -> List (Maybe Name, RawImp FC) -> List (Name, RawImp FC)
    nameCons i [] = []
    nameCons i ((_, ty) :: rest) 
        = (UN ("__con" ++ show i), ty) :: nameCons (i + 1) rest

    -- Elaborate the data declaration part of the interface
    elabAsData : (conName : Name) ->
                 List (FC, Name, RawImp FC) ->
                 Core FC ()
    elabAsData conName meth_sigs
        = do let meths = map (getMethDecl env nest params) meth_sigs
             let dt = mkIfaceData fc vis env constraints iname conName params 
                                  dets meths
             log 10 $ "Methods: " ++ show meths
             processDecls env nest [dt]
             log 5 $ "Made interface data type " ++ show dt

    elabMethods : (conName : Name) -> List Name -> 
                  List (FC, Name, RawImp FC) ->
                  Core FC ()
    elabMethods conName meth_names meth_sigs
        = do -- Methods have same visibility as data declaration
             let fns = concatMap (getMethToplevel env vis iname conName
                                                  (map fst constraints)
                                                  meth_names
                                                  (map fst params)) meth_sigs
             log 5 $ "Top level methods: " ++ show fns
             traverse (processDecl env nest) fns
             pure ()

    elabConstraintHints : (conName : Name) -> List Name ->
                          Core FC()
    elabConstraintHints conName meth_names
        = do let nconstraints = nameCons 0 constraints
             let chints = concatMap (getConstraintHint fc env vis iname conName
                                                       (map fst nconstraints)
                                                       meth_names
                                                       (map fst params)) nconstraints
             log 5 $ "Constraint hints from " ++ show constraints ++ ": " ++ show chints
             traverse (processDecl env nest) chints
             pure ()

