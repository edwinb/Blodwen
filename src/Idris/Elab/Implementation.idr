module Idris.Elab.Implementation

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

mkImpl : Name -> List (RawImp FC) -> Name
mkImpl n ps = MN ("__Impl_" ++ show n ++ "_" ++
                  showSep "_" (map show ps)) 0

bindConstraints : FC -> PiInfo -> 
                  List (Maybe Name, RawImp FC) -> RawImp FC -> RawImp FC
bindConstraints fc p [] ty = ty
bindConstraints fc p ((n, ty) :: rest) sc
    = IPi fc RigW p n ty (bindConstraints fc p rest sc)

mutual
  substParams : List Name -> List (Name, RawImp FC) -> RawImp FC -> RawImp FC
  substParams bound ps (IVar fc n) 
      = if not (n `elem` bound)
           then case lookup n ps of
                     Just t => t
                     _ => IVar fc n
           else IVar fc n
  substParams bound ps (IPi fc r p mn argTy retTy) 
      = let bound' = maybe bound (\n => n :: bound) mn in
            IPi fc r p mn (substParams bound ps argTy) 
                          (substParams bound' ps retTy)
  substParams bound ps (ILam fc r p n argTy scope)
      = let bound' = n :: bound in
            ILam fc r p n (substParams bound ps argTy) 
                          (substParams bound' ps scope)
  substParams bound ps (ILet fc r n nTy nVal scope)
      = let bound' = n :: bound in
            ILet fc r n (substParams bound ps nTy) 
                        (substParams bound ps nVal)
                        (substParams bound' ps scope)
  substParams bound ps (ICase fc y ty xs) 
      = ICase fc (substParams bound ps y) (substParams bound ps ty)
                 (map (substParamsClause bound ps) xs)
  substParams bound ps (ILocal fc xs y) 
      = let bound' = definedInBlock xs ++ bound in
            ILocal fc (map (substParamsDecl bound ps) xs) 
                      (substParams bound' ps y)
  substParams bound ps (IApp fc fn arg) 
      = IApp fc (substParams bound ps fn) (substParams bound ps arg)
  substParams bound ps (IImplicitApp fc fn y arg)
      = IImplicitApp fc (substParams bound ps fn) y (substParams bound ps arg)
  substParams bound ps (IAlternative fc y xs) 
      = IAlternative fc y (map (substParams bound ps) xs)
  substParams bound ps (ICoerced fc y) 
      = ICoerced fc (substParams bound ps y)
  substParams bound ps (IQuote fc y)
      = IQuote fc (substParams bound ps y)
  substParams bound ps (IUnquote fc y)
      = IUnquote fc (substParams bound ps y)
  substParams bound ps (IAs fc y pattern)
      = IAs fc y (substParams bound ps pattern)
  substParams bound ps (IMustUnify fc pattern)
      = IMustUnify fc (substParams bound ps pattern)
  substParams bound ps tm = tm

  substParamsClause : List Name -> List (Name, RawImp FC) -> 
                      ImpClause FC -> ImpClause FC
  substParamsClause bound ps (PatClause fc lhs rhs)
      = let bound' = map UN (findBindableNames True bound lhs) ++ bound in
            PatClause fc (substParams [] [] lhs) 
                         (substParams bound' ps rhs)
  substParamsClause bound ps (ImpossibleClause fc lhs)
      = ImpossibleClause fc (substParams bound [] lhs)

  substParamsTy : List Name -> List (Name, RawImp FC) ->
                  ImpTy FC -> ImpTy FC
  substParamsTy bound ps (MkImpTy fc n ty) 
      = MkImpTy fc n (substParams bound ps ty)
  
  substParamsData : List Name -> List (Name, RawImp FC) ->
                    ImpData FC -> ImpData FC
  substParamsData bound ps (MkImpData fc n con opts dcons) 
      = MkImpData fc n (substParams bound ps con) opts
                  (map (substParamsTy bound ps) dcons)
  substParamsData bound ps (MkImpLater fc n con) 
      = MkImpLater fc n (substParams bound ps con)

  substParamsDecl : List Name -> List (Name, RawImp FC) ->
                    ImpDecl FC -> ImpDecl FC
  substParamsDecl bound ps (IClaim fc vis opts td) 
      = IClaim fc vis opts (substParamsTy bound ps td)
  substParamsDecl bound ps (IDef fc n cs) 
      = IDef fc n (map (substParamsClause bound ps) cs)
  substParamsDecl bound ps (IData fc vis d) 
      = IData fc vis (substParamsData bound ps d)
  substParamsDecl bound ps (INamespace fc ns ds) 
      = INamespace fc ns (map (substParamsDecl bound ps) ds)
  substParamsDecl bound ps (IReflect fc y) 
      = IReflect fc (substParams bound ps y)
  substParamsDecl bound ps (ImplicitNames fc xs) 
      = ImplicitNames fc (map (\ (n, t) => (n, substParams bound ps t)) xs)
  substParamsDecl bound ps d = d

export
elabImplementation : {auto c : Ref Ctxt Defs} ->
                     {auto u : Ref UST (UState FC)} ->
                     {auto i : Ref ImpST (ImpState FC)} ->
                     {auto s : Ref Syn SyntaxInfo} ->
                     FC -> Visibility -> 
                     Env Term vars -> NestedNames vars ->
                     (constraints : List (Maybe Name, RawImp FC)) ->
                     Name ->
                     (ps : List (RawImp FC)) ->
                     (implName : Maybe Name) ->
                     List (ImpDecl FC) ->
                     Core FC ()
elabImplementation {vars} fc vis env nest cons iname ps impln body
    = do let impName_in = maybe (mkImpl iname ps) id impln
         impName <- inCurrentNS impName_in
         syn <- get Syn
         cndata <- case lookupCtxtName iname (ifaces syn) of
                        [] => throw (UndefinedName fc iname)
                        [i] => pure i
                        ns => throw (AmbiguousName fc (map fst ns))
         let cn : Name = fst cndata
         let cdata : IFaceInfo = snd cndata
         defs <- get Ctxt

         ity <- case lookupTyExact cn (gamma defs) of
                     Nothing => throw (UndefinedName fc cn)
                     Just t => pure t

         log 0 $ "Found interface " ++ show cn ++ " : "
                 ++ show (normaliseHoles defs [] ity)
                 ++ " with params: " ++ show (params cdata)
                 ++ " and methods: " ++ show (methods cdata) ++ "\n"
                 ++ "Constructor: " ++ show (iconstructor cdata)

         -- 1. Build the type for the implementation
         --    {auto cs : Constraints} -> Impl params
         let impTy = bindTypeNames fc vars $
                     bindConstraints fc Explicit cons 
                         (apply (IVar fc iname) ps)
         let impTyDecl = IClaim fc vis [Inline, Hint] (MkImpTy fc impName impTy)
         processDecl env nest impTyDecl

         -- 2. Elaborate top level function types for this interface
         defs <- get Ctxt
         traverse (topMethType defs impName (params cdata) ity) 
                  (methods cdata)

         -- 3. (TODO: Generate default method bodies)

         -- 4. Elaborate the method bodies

         -- 5. Check that every top level function type has a definition now

         -- 6. Build the record for the implementation

         throw (InternalError "Implementations not done yet")
  where
    methName : Name -> Name
    methName (NS _ n) = methName n
    methName n = MN (show n ++ "_" ++ show iname ++ "_" ++
                     showSep "_" (map show ps)) 0
    
    topMethType : Defs -> Name -> List Name -> ClosedTerm -> 
                  (Name, RawImp FC) -> 
                  Core FC ()
    topMethType defs impName pnames ity (mn, mty_in)
        = do -- Get the specialised type by applying the method to the
             -- parameters
             n <- inCurrentNS (methName mn)

             let mty = bindConstraints fc AutoImplicit cons $
                       substParams vars (zip pnames ps) mty_in

             log 0 $ "Method " ++ show n ++ " : " ++ show mty
             log 0 $ "Parameters: " ++ show (zip pnames ps)
             log 0 $ "Constraints: " ++ show cons
             

--              let specMeth = applyParams (zip pnames ps) 
--                               (IImplicitApp fc (IVar fc mn)
--                                                (MN "__con" 0)
--                                                (IVar fc impName))
--              -- Use 'inTmpState' because we don't want to keep the holes
--              -- that might result
--              log 0 $ "Specialise as " ++ show specMeth
--              (tm, ty) <- inTmpState $
--                     inferTerm elabTop (UN "[method spec]") env nest
--                               NONE InExpr specMeth
--              n <- inCurrentNS (methName mn)
-- 
--              let mty = mkSpecTy (gamma defs) (snd (getFnArgs tm)) (embed fty)
-- 
--              log 0 $ "Method " ++ show mn ++ " specialised to " ++ show tm
--              log 0 $ "Method " ++ show n ++ " type " ++ 
--                                   show (normaliseHoles defs env mty)

{-
    applyParams : List (Name, RawImp FC) -> RawImp FC -> RawImp FC
    applyParams [] tm = tm
    applyParams ((n, t) :: rest) tm
        = IImplicitApp fc (applyParams rest tm) n t

    isUndefined : Gamma -> Term vs -> Bool
    isUndefined gam tm
        = case getFn tm of
               Ref _ n => case lookupTyExact n gam of
                               Nothing => True
                               _ => False
               _ => False

    mkSpecTy : Gamma -> List (Term vs) -> Term vs -> Term vs
    mkSpecTy gam (a :: as) (Bind n (Pi c p ty) sc) 
        = -- if 'a' is a reference to something that doesn't exist,
          -- it was a hole after checking the specialised application,
          -- so leave it alone here
          if isUndefined gam a
             then Bind n (Pi c p ty) (mkSpecTy gam (map weaken as) sc)
             else mkSpecTy gam as (subst a sc)
    mkSpecTy gam _ ty = ty
    -}

          
--           case lookupTyExact mn gam of
--                Nothing => throw (UndefinedName fc mn)
--                Just ty =>
--                   do let mty = specMethType ty
--                      n <- inCurrentNS (methName mn)
--                      log 0 $ "Method " ++ show n ++ " type " ++
--                             show mty
--                      pure (n, mty)

