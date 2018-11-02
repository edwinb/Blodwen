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

mkDataTy : FC -> List (Name, RawImp FC) -> RawImp FC
mkDataTy fc [] = IType fc
mkDataTy fc ((n, ty) :: ps) 
    = IPi fc RigW Explicit (Just n) ty (mkDataTy fc ps)

mkCon : FC -> Name -> Name
mkCon loc (NS ns (UN n)) = NS ns (DN (n ++ " at " ++ show loc) (MN ("__mk" ++ n) 0))
mkCon loc n = DN (show n ++ " at " ++ show loc) (MN ("__mk" ++ show n) 0)

export
elabRecord : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState FC)} ->
             {auto i : Ref ImpST (ImpState FC)} ->
             {auto s : Ref Syn SyntaxInfo} ->
             {auto m : Ref Meta (Metadata FC)} ->
             FC -> Visibility -> 
             Env Term vars -> NestedNames vars ->
             Name ->
             (params : List (Name, RawImp FC)) ->
             (conName : Maybe Name) ->
             List (FC, RigCount, PiInfo, Name, RawImp FC) ->
             Core FC ()
elabRecord {vars} fc vis env nest tn params rcon fields 
    = do let conName_in = maybe (mkCon fc tn) id rcon
         conName <- inCurrentNS conName_in
         elabAsData conName
         defs <- get Ctxt
         let Just conty = lookupTyExact conName (gamma defs)
             | Nothing => throw (InternalError ("Adding " ++ show tn ++ "failed"))
         let recTy = apply (IVar fc tn) (map (IVar fc) (map fst params))
         elabGetters conName recTy 0 [] [] conty
  where
    jname : (Name, RawImp FC) -> (Maybe Name, RigCount, PiInfo, RawImp FC)
    jname (n, t) = (Just n, Rig0, Implicit, t)

    fname : (FC, RigCount, PiInfo, Name, RawImp FC) -> Name
    fname (fc, c, p, n, ty) = n

    farg : (FC, RigCount, PiInfo, Name, RawImp FC) -> 
           (Maybe Name, RigCount, PiInfo, RawImp FC)
    farg (fc, c, p, n, ty) = (Just n, c, p, ty)
    
    mkTy : List (Maybe Name, RigCount, PiInfo, RawImp FC) -> 
           RawImp FC -> RawImp FC
    mkTy [] ret = ret
    mkTy ((n, c, imp, argty) :: args) ret
        = IPi fc c imp n argty (mkTy args ret)

    elabAsData : Name -> Core FC ()
    elabAsData cname 
        = do let retty = apply (IVar fc tn) (map (IVar fc) (map fst params))
             let conty = mkTy (map jname params) $
                         mkTy (map farg fields) retty
             let con = MkImpTy fc cname (bindTypeNames (map fst params ++
                                           map fname fields ++ vars) conty)
             let dt = MkImpData fc tn (bindTypeNames (map fst params ++
                                           map fname fields ++ vars)
                                         (mkDataTy fc params)) [] [con]
             log 5 $ "Record data type " ++ show dt
             processDecls env nest [IData fc vis dt]

    impName : Name -> Name
    impName (UN n) = UN ("imp_" ++ n)
    impName n = n

    countExp : Term vs -> Nat
    countExp (Bind n (Pi c Explicit _) sc) = S (countExp sc)
    countExp (Bind n (Pi c _ _) sc) = countExp sc
    countExp _ = 0

    -- Oops, needs to be done from the elaborated type, not the raw type!
    elabGetters : Name -> RawImp FC -> (done : Nat) ->
                  List (Name, RawImp FC) -> Env Term vs -> Term vs ->
                  Core FC ()
    elabGetters con recTy done upds tyenv (Bind n b@(Pi c imp ty_chk) sc)
        = if n `elem` map fst params
             then elabGetters con recTy
                              (if imp == Explicit 
                                  then S done else done)
                              upds (b :: tyenv) sc
             else 
                do let fldName = case imp of
                                      Explicit => n
                                      _ => impName n
                   gname <- inCurrentNS fldName
                   ty <- unelab fc tyenv ty_chk

                   let ty' = substNames vars upds ty
                   let rname = MN "rec" 0
                   let gty = bindTypeNames 
                                 (map fst params ++ map fname fields ++ vars) $
                                    mkTy (map jname params) $
                                      IPi fc RigW Explicit (Just rname) recTy ty'
                   log 5 $ "Projection " ++ show gname ++ " : " ++ show gty

                   let lhs_exp = apply (IVar fc con)
                                    (replicate done (Implicit fc) ++
                                       (if imp == Explicit
                                           then [IBindVar fc (nameRoot fldName)]
                                           else []) ++ 
                                    (replicate (countExp sc) (Implicit fc)))
                   let lhs = IApp fc (IVar fc gname)
                                (if imp == Explicit
                                    then lhs_exp
                                    else IImplicitApp fc lhs_exp (Just n)
                                             (IBindVar fc (nameRoot fldName)))
                   log 5 $ show lhs ++ " = " ++ show fldName

                   processDecls env nest 
                       [IClaim fc (if c == Rig0
                                      then Rig0
                                      else RigW) vis [] (MkImpTy fc gname gty),
                        IDef fc gname [PatClause fc lhs (IVar fc fldName)]]

                   let upds' = (n, IApp fc (IVar fc gname) (IVar fc rname)) :: upds
                   elabGetters con recTy
                               (if imp == Explicit 
                                   then S done else done)
                               upds' (b :: tyenv) sc
    elabGetters con recTy done upds _ _ = pure ()
