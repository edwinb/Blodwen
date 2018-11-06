module TTImp.ProcessRecord

import Core.Binary
import Core.Context
import Core.Core
import Core.Metadata
import Core.TT
import Core.Unify

import TTImp.BindImplicits
import TTImp.Elab
import TTImp.Elab.Unelab
import TTImp.Reflect
import TTImp.TTImp
import TTImp.Utils

mkDataTy : annot -> List (Name, RawImp annot) -> RawImp annot
mkDataTy fc [] = IType fc
mkDataTy fc ((n, ty) :: ps) 
    = IPi fc RigW Explicit (Just n) ty (mkDataTy fc ps)

mkCon : annot -> Name -> Name
mkCon loc (NS ns (UN n)) = NS ns (DN n (MN ("__mk" ++ n) 0))
mkCon loc n = DN (show n) (MN ("__mk" ++ show n) 0)

elabRecord : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             {auto i : Ref ImpST (ImpState annot)} ->
             {auto m : Ref Meta (Metadata annot)} ->
             Reflect annot =>
             Elaborator annot ->
             annot -> Env Term vars -> NestedNames vars -> Visibility ->
             Name ->
             (params : List (Name, RawImp annot)) ->
             (conName : Maybe Name) ->
             List (IField annot) ->
             Core annot ()
elabRecord {c} {u} {i} {m} {vars} elab fc env nest vis tn params rcon fields 
    = do let conName_in = maybe (mkCon fc tn) id rcon
         conName <- inCurrentNS conName_in
         elabAsData conName
         defs <- get Ctxt
         let Just conty = lookupTyExact conName (gamma defs)
             | Nothing => throw (InternalError ("Adding " ++ show tn ++ "failed"))
         let recTy = apply (IVar fc tn) (map (IVar fc) (map fst params))
         elabGetters conName recTy 0 [] [] conty
  where
    jname : (Name, RawImp annot) -> (Maybe Name, RigCount, PiInfo, RawImp annot)
    jname (n, t) = (Just n, Rig0, Implicit, t)

    fname : IField annot -> Name
    fname (MkIField fc c p n ty) = n

    farg : IField annot -> 
           (Maybe Name, RigCount, PiInfo, RawImp annot)
    farg (MkIField fc c p n ty) = (Just n, c, p, ty)
    
    mkTy : List (Maybe Name, RigCount, PiInfo, RawImp annot) -> 
           RawImp annot -> RawImp annot
    mkTy [] ret = ret
    mkTy ((n, c, imp, argty) :: args) ret
        = IPi fc c imp n argty (mkTy args ret)

    elabAsData : Name -> Core annot ()
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
             elab c u i m False env nest (IData fc vis dt)

    impName : Name -> Name
    impName (UN n) = UN ("imp_" ++ n)
    impName n = n

    countExp : Term vs -> Nat
    countExp (Bind n (Pi c Explicit _) sc) = S (countExp sc)
    countExp (Bind n (Pi c _ _) sc) = countExp sc
    countExp _ = 0

    -- Generate getters from the elaborated record constructor type
    elabGetters : Name -> RawImp annot -> 
                  (done : Nat) -> -- number of explicit fields processed
                  List (Name, RawImp annot) -> -- names to update in types
                    -- (for dependent records, where a field's type may depend
                    -- on an earlier projection)
                  Env Term vs -> Term vs ->
                  Core annot ()
    elabGetters con recTy done upds tyenv (Bind n b@(Pi rc imp ty_chk) sc)
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

                   elab c u i m False env nest 
                       (IClaim fc (if rc == Rig0
                                      then Rig0
                                      else RigW) vis [] (MkImpTy fc gname gty))
                   elab c u i m False env nest
                       (IDef fc gname [PatClause fc lhs (IVar fc fldName)])

                   let upds' = (n, IApp fc (IVar fc gname) (IVar fc rname)) :: upds
                   elabGetters con recTy
                               (if imp == Explicit 
                                   then S done else done)
                               upds' (b :: tyenv) sc
    elabGetters con recTy done upds _ _ = pure ()

export
processRecord : {auto c : Ref Ctxt Defs} ->
                {auto u : Ref UST (UState annot)} ->
                {auto i : Ref ImpST (ImpState annot)} ->
                {auto m : Ref Meta (Metadata annot)} ->
                Reflect annot =>
                Elaborator annot ->
                Env Term vars -> NestedNames vars ->
                Visibility -> 
                ImpRecord annot ->
                Core annot ()
processRecord elab env nest vis (MkImpRecord loc n ps con fs)
    = elabRecord elab loc env nest vis n ps con fs
