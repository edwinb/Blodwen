module Idris.Elab.Interface

import Core.Binary
import Core.Context
import Core.Core
import Core.Metadata
import Core.TT
import Core.Unify

import Idris.BindImplicits
import Idris.Resugar
import Idris.Syntax

import TTImp.ProcessTTImp
import TTImp.Elab
import TTImp.Elab.Unelab
import TTImp.TTImp
import TTImp.Utils

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
                  mkTy Explicit RigW (map bhere constraints ++ map bname meths) retty
          con = MkImpTy fc conName (bindTypeNames (map fst ps ++ map fst meths ++ vars) conty) in
          IData fc vis (MkImpData fc n 
                                  (bindTypeNames (map fst ps ++ map fst meths ++ vars)
                                                 (mkDataTy fc ps)) 
                                  opts [con])
  where
    jname : (Name, RawImp FC) -> (Maybe Name, RawImp FC)
    jname (n, t) = (Just n, t)

    bname : (Name, RawImp FC) -> (Maybe Name, RawImp FC)
    bname (n, t) = (Just n, IBindHere (getAnnot t) t)

    bhere : (Maybe Name, RawImp FC) -> (Maybe Name, RawImp FC)
    bhere (n, t) = (n, IBindHere (getAnnot t) t)

    mkTy : PiInfo -> RigCount ->
           List (Maybe Name, RawImp FC) -> RawImp FC -> RawImp FC
    mkTy imp c [] ret = ret
    mkTy imp c ((n, argty) :: args) ret
        = IPi fc c imp n argty (mkTy imp c args ret)

-- Get the implicit arguments for a method declaration or constraint hint
-- to allow us to build the data declaration
getMethDecl : Env Term vars -> NestedNames vars ->
              (params : List (Name, RawImp FC)) ->
              (mnames : List Name) ->
              (FC, List FnOpt, n, (Bool, RawImp FC)) -> (n, RawImp FC)
getMethDecl {vars} env nest params mnames (fc, opts, n, (d, ty))
    = let ty_imp = bindTypeNames (map fst params ++ mnames ++ vars) ty in
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
    
-- bind the auto implicit for the interface - put it after all the other
-- implicits
bindIFace : FC -> RawImp FC -> RawImp FC -> RawImp FC
bindIFace _ ity (IPi fc rig Implicit n ty sc)
       = IPi fc rig Implicit n ty (bindIFace fc ity sc)
bindIFace _ ity (IPi fc rig AutoImplicit n ty sc)
       = IPi fc rig AutoImplicit n ty (bindIFace fc ity sc)
bindIFace fc ity sc = IPi fc RigW AutoImplicit (Just (MN "__con" 0)) ity sc


-- Get the top level function for implementing a method 
getMethToplevel : {auto c : Ref Ctxt Defs} ->
                  {auto u : Ref UST (UState FC)} ->
                  {auto i : Ref ImpST (ImpState FC)} ->
                  {auto m : Ref Meta (Metadata FC)} ->
                  Env Term vars -> Visibility -> 
                  Name -> Name ->
                  (constraints : List (Maybe Name)) ->
                  (allmeths : List Name) ->
                  (params : List Name) ->
                  (FC, List FnOpt, Name, (Bool, RawImp FC)) -> 
                  List (ImpDecl FC)
getMethToplevel {vars} env vis iname cname constraints allmeths params (fc, opts, n, (d, ty))
    = let ity = apply (IVar fc iname) (map (IVar fc) params) 
          -- Make the constraint application explicit for any method names
          -- which appear in other method types
          ty_constr = substNames vars (map applyCon allmeths) ty
          ty_imp = bindTypeNames vars (bindIFace fc ity ty_constr)
          tydecl = IClaim fc RigW vis (if d then [Inline, Invertible]
                                            else [Inline]) (MkImpTy fc n ty_imp) 
          conapp = apply (IVar fc cname)
                      (map (const (Implicit fc)) constraints ++
                       map (IBindVar fc) (map bindName allmeths))
          argns = getExplicitArgs 0 ty
          -- eta expand the RHS so that we put implicits in the right place
          fnclause = PatClause fc (IImplicitApp fc (IVar fc n) 
                                                   (Just (MN "__con" 0))
                                                   conapp)
                                  (mkLam argns 
                                    (apply (IVar fc (methName n))
                                           (map (IVar fc) argns)))
          fndef = IDef fc n [fnclause] in
          [tydecl, fndef]
  where
    applyCon : Name -> (Name, RawImp FC)
    applyCon n = (n, IImplicitApp fc (IVar fc n) 
                             (Just (MN "__con" 0)) (IVar fc (MN "__con" 0)))

    getExplicitArgs : Int -> RawImp FC -> List Name
    getExplicitArgs i (IPi _ _ Explicit n _ sc)
        = MN "arg" i :: getExplicitArgs (i + 1) sc
    getExplicitArgs i (IPi _ _ _ n _ sc) = getExplicitArgs i sc
    getExplicitArgs i tm = []

    mkLam : List Name -> RawImp FC -> RawImp FC
    mkLam [] tm = tm
    mkLam (x :: xs) tm = ILam fc RigW Explicit (Just x) (Implicit fc) (mkLam xs tm)

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
                    {auto m : Ref Meta (Metadata FC)} ->
                    FC -> Env Term vars -> Visibility -> 
                    Name -> Name ->
                    (constraints : List Name) ->
                    (allmeths : List Name) ->
                    (params : List Name) ->
                    (Name, RawImp FC) -> List (ImpDecl FC)
getConstraintHint {vars} fc env vis iname cname constraints meths params (cn, con)
    = let ity = apply (IVar fc iname) (map (IVar fc) params)
          fty = IPi fc RigW Explicit Nothing ity con
          ty_imp = bindTypeNames (meths ++ vars) fty 
          hintname = DN ("Constraint " ++ show con)
                        (MN ("__" ++ show iname ++ "_" ++ show con) 0)
          tydecl = IClaim fc RigW vis [Inline, Hint False] (MkImpTy fc hintname ty_imp)
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

getSig : ImpDecl FC -> Maybe (FC, List FnOpt, Name, (Bool, RawImp FC))
getSig (IClaim _ _ _ opts (MkImpTy fc n ty)) = Just (fc, opts, n, (False, ty))
getSig (IData _ _ (MkImpLater fc n ty)) = Just (fc, [Invertible], n, (True, ty))
getSig _ = Nothing

getDefault : ImpDecl FC -> Maybe (FC, List FnOpt, Name, List (ImpClause FC))
getDefault (IDef fc n cs) = Just (fc, [], n, cs)
getDefault _ = Nothing

mkCon : FC -> Name -> Name
mkCon loc (NS ns (UN n)) = NS ns (DN (n ++ " at " ++ show loc) (MN ("__mk" ++ n) 0))
mkCon loc n = DN (show n ++ " at " ++ show loc) (MN ("__mk" ++ show n) 0)

updateIfaceSyn : {auto s : Ref Syn SyntaxInfo} ->
                 Name -> Name -> List Name -> List (RawImp FC) ->
                 List (Name, (Bool, RawImp FC)) -> List (Name, List (ImpClause FC)) ->
                 Core FC ()
updateIfaceSyn iname cn ps cs ms ds
    = do syn <- get Syn
         let info = MkIFaceInfo cn ps cs ms ds
         put Syn (record { ifaces $= addCtxt iname info } syn)

export
elabInterface : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState FC)} ->
                {auto i : Ref ImpST (ImpState FC)} ->
                {auto s : Ref Syn SyntaxInfo} ->
                {auto m : Ref Meta (Metadata FC)} ->
                FC -> Visibility -> 
                Env Term vars -> NestedNames vars ->
                (constraints : List (Maybe Name, RawImp FC)) ->
                Name ->
                (params : List (Name, RawImp FC)) ->
                (dets : List Name) ->
                (conName : Maybe Name) ->
                List (ImpDecl FC) ->
                Core FC ()
elabInterface {vars} fc vis env nest constraints iname params dets mcon body
    = do let conName_in = maybe (mkCon fc iname) id mcon
         -- Machine generated names need to be qualified when looking them up
         conName <- inCurrentNS conName_in
         let meth_sigs = mapMaybe getSig body -- (FC, List FnOpt, Name, RawImp FC)
         let meth_decls = map (snd . snd) meth_sigs -- (Name, RawImp FC)
         let meth_names = map fst meth_decls
         let defaults = mapMaybe getDefault body

         elabAsData conName meth_names meth_sigs
         elabConstraintHints conName meth_names
         elabMethods conName meth_names meth_sigs
         ds <- traverse (elabDefault meth_decls) defaults

         ns_meths <- traverse (\mt => do n <- inCurrentNS (fst mt)
                                         pure (n, snd mt)) meth_decls
         ns_iname <- inCurrentNS iname
         updateIfaceSyn ns_iname conName 
                        (map fst params) (map snd constraints)
                        ns_meths ds
  where
    nameCons : Int -> List (Maybe Name, RawImp FC) -> List (Name, RawImp FC)
    nameCons i [] = []
    nameCons i ((_, ty) :: rest) 
        = (UN ("__con" ++ show i), ty) :: nameCons (i + 1) rest

    -- Elaborate the data declaration part of the interface
    elabAsData : (conName : Name) -> List Name ->
                 List (FC, List FnOpt, Name, (Bool, RawImp FC)) ->
                 Core FC ()
    elabAsData conName meth_names meth_sigs
        = do -- set up the implicit arguments correctly in the method
             -- signatures and constraint hints
             let meths = map (getMethDecl env nest params meth_names) meth_sigs
             log 5 $ "Method declarations: " ++ show meths
             
             let consts = map (getMethDecl env nest params meth_names) 
                              (map (\c => (fc, [], c))
                                 (map notData constraints))
             log 5 $ "Constraints: " ++ show consts

             let dt = mkIfaceData fc vis env consts iname conName params 
                                  dets meths
             log 10 $ "Methods: " ++ show meths
             processDecls env nest [dt]
             log 5 $ "Made interface data type " ++ show dt
      where
        notData : (n, t) -> (n, (Bool, t))
        notData (x, y) = (x, (False, y))

    elabMethods : (conName : Name) -> List Name -> 
                  List (FC, List FnOpt, Name, (Bool, RawImp FC)) ->
                  Core FC ()
    elabMethods conName meth_names meth_sigs
        = do -- Methods have same visibility as data declaration
             let fns = concatMap (getMethToplevel env vis iname conName
                                                  (map fst constraints)
                                                  meth_names
                                                  (map fst params)) meth_sigs
             log 5 $ "Top level methods: " ++ show fns
             traverse (processDecl False env nest) fns
             pure ()

    -- Check that a default definition is correct. We just discard it here once
    -- we know it's okay, since we'll need to re-elaborate it for each
    -- instance, to specialise it
    elabDefault : List (Name, (Bool, RawImp FC)) ->
                  (FC, List FnOpt, Name, List (ImpClause FC)) -> 
                  Core FC (Name, List (ImpClause FC))
    elabDefault tydecls (fc, opts, n, cs) 
        = do orig <- get Ctxt
             let dn_in = UN ("Default implementation of " ++ show n)
             dn <- inCurrentNS dn_in

             dty <- case lookup n tydecls of
                         Just (_, t) => pure t
                         Nothing => throw (GenericMsg fc ("No method named " ++ show n ++ " in interface " ++ show iname))
             log 5 $ "Default method " ++ show dn ++ " : " ++ show dty
                  
             let ity = apply (IVar fc iname) (map (IVar fc) (map fst params))
             let dty_imp = bindTypeNames vars (bindIFace fc ity dty)
             let dtydecl = IClaim fc RigW vis [] (MkImpTy fc dn dty_imp) 
             processDecl False env nest dtydecl

             let cs' = map (changeName dn) cs
             processDecl False env nest (IDef fc dn cs')
             -- Reset the original context, we don't need to keep the definition
             put Ctxt orig
             pure (n, cs)
      where
        changeNameTerm : Name -> RawImp FC -> RawImp FC
        changeNameTerm dn (IVar fc n')
            = if n == n' then IVar fc dn else IVar fc n'
        changeNameTerm dn (IApp fc f arg)
            = IApp fc (changeNameTerm dn f) arg
        changeNameTerm dn (IImplicitApp fc f x arg)
            = IImplicitApp fc (changeNameTerm dn f) x arg
        changeNameTerm dn tm = tm

        changeName : Name -> ImpClause FC -> ImpClause FC
        changeName dn (PatClause fc lhs rhs) 
            = PatClause fc (changeNameTerm dn lhs) rhs
        changeName dn (ImpossibleClause fc lhs) 
            = ImpossibleClause fc (changeNameTerm dn lhs)

    elabConstraintHints : (conName : Name) -> List Name ->
                          Core FC ()
    elabConstraintHints conName meth_names
        = do let nconstraints = nameCons 0 constraints
             let chints = concatMap (getConstraintHint fc env vis iname conName
                                                       (map fst nconstraints)
                                                       meth_names
                                                       (map fst params)) nconstraints
             log 5 $ "Constraint hints from " ++ show constraints ++ ": " ++ show chints
             traverse (processDecl False env nest) chints
             pure ()

