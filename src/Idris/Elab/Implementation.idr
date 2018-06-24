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

         log 3 $ "Found interface " ++ show cn ++ " : "
                 ++ show (normaliseHoles defs [] ity)
                 ++ " with params: " ++ show (params cdata)
                 ++ " and methods: " ++ show (methods cdata) ++ "\n"
                 ++ "Constructor: " ++ show (iconstructor cdata)
         log 5 $ "Making implementation " ++ show impName

         -- 1. Build the type for the implementation
         -- Make the constraints auto implicit arguments, which can be explicitly
         -- given when using named implementations
         --    (cs : Constraints) -> Impl params
         -- Don't make it a hint if it's a named implementation
         let opts = maybe [Inline, Hint] (const [Inline]) impln

         let impTy = bindTypeNames vars $
                     bindConstraints fc AutoImplicit cons 
                         (apply (IVar fc iname) ps)
         let impTyDecl = IClaim fc vis opts (MkImpTy fc impName impTy)
         processDecl env nest impTyDecl

         -- 2. Elaborate top level function types for this interface
         defs <- get Ctxt
         fns <- traverse (topMethType impName (params cdata)) 
                         (methods cdata)
         processDecls env nest (map mkTopMethDecl fns)

         -- 3. Build the record for the implementation
         let mtops = map (Basics.fst . snd) fns
         let con = iconstructor cdata
         let ilhs = IVar fc impName
         let irhs = apply (IVar fc con) (map mkMethField (map Basics.snd fns))
         let impFn = IDef fc impName [PatClause fc ilhs irhs]
         log 5 $ "Implementation record: " ++ show impFn
         processDecls env nest [impFn]

         -- 4. (TODO: Generate default method bodies)

         -- 5. Elaborate the method bodies

         -- If it's a named implementation, add it as a global hint while
         -- elaborating the bodies
         defs <- get Ctxt
         let hs = openHints defs
         maybe (pure ()) (\x => addOpenHint impName) impln

         body' <- traverse (updateBody (map methNameUpdate fns)) body
         log 10 $ "Implementation body: " ++ show body'
         processDecls env nest body'
         -- Reset the open hints (remove the named implementation)
         setOpenHints hs

         -- 6. Check that every top level function type has a definition now


         pure () -- throw (InternalError "Implementations not done yet")
  where
    getExplicitArgs : Int -> RawImp FC -> List Name
    getExplicitArgs i (IPi _ _ Explicit n _ sc)
        = MN "arg" i :: getExplicitArgs (i + 1) sc
    getExplicitArgs i (IPi _ _ _ n _ sc) = getExplicitArgs i sc
    getExplicitArgs i tm = []

    mkLam : List Name -> RawImp FC -> RawImp FC
    mkLam [] tm = tm
    mkLam (x :: xs) tm = ILam fc RigW Explicit x (Implicit fc) (mkLam xs tm)

    -- When applying the method in the field for the record, eta expand
    -- the explicit arguments so that implicits get inserted in the right 
    -- place
    mkMethField : (Name, RawImp FC) -> RawImp FC
    mkMethField (n, ty) 
        = let argns = getExplicitArgs 0 ty in
              mkLam argns (apply (IVar fc n) (map (IVar fc) argns))

    methName : Name -> Name
    methName (NS _ n) = methName n
    methName n = MN (show n ++ "_" ++ show iname ++ "_" ++
                     maybe "" show impln ++ "_" ++
                     showSep "_" (map show ps)) 0
    
    topMethType : Name -> List Name -> (Name, RawImp FC) -> 
                  Core FC (Name, Name, RawImp FC)
    topMethType impName pnames (mn, mty_in)
        = do -- Get the specialised type by applying the method to the
             -- parameters
             n <- inCurrentNS (methName mn)

             let mty = bindTypeNames vars $
                       bindConstraints fc AutoImplicit cons $
                       substParams vars (zip pnames ps) mty_in

             log 3 $ "Method " ++ show mn ++ " ==> " ++
                     show n ++ " : " ++ show mty
             pure (mn, n, mty)
             
    mkTopMethDecl : (Name, Name, RawImp FC) -> ImpDecl FC
    mkTopMethDecl (mn, n, mty) = IClaim fc vis [Inline] (MkImpTy fc n mty)

    -- Given the method type (result of topMethType) return the mapping from
    -- top level method name to current implementation's method name
    methNameUpdate : (Name, Name, t) -> (Name, Name)
    methNameUpdate (mn, fn, _) = (UN (nameRoot mn), fn)

    findMethName : List (Name, Name) -> FC -> Name -> Core FC Name
    findMethName ns fc n
        = case lookup n ns of
               Nothing => throw (GenericMsg fc 
                                (show n ++ " is not a method of " ++ 
                                 show iname))
               Just n' => pure n'

    updateApp : List (Name, Name) -> RawImp FC -> Core FC (RawImp FC)
    updateApp ns (IVar fc n)
        = do n' <- findMethName ns fc n
             pure (IVar fc n')
    updateApp ns (IApp fc f arg)
        = do f' <- updateApp ns f
             pure (IApp fc f' arg)
    updateApp ns (IImplicitApp fc f x arg)
        = do f' <- updateApp ns f
             pure (IImplicitApp fc f' x arg)
    updateApp ns tm
        = throw (GenericMsg (getAnnot tm) "Invalid method definition")

    updateClause : List (Name, Name) -> ImpClause FC -> 
                   Core FC (ImpClause FC)
    updateClause ns (PatClause fc lhs rhs) 
        = do lhs' <- updateApp ns lhs
             pure (PatClause fc lhs' rhs)
    updateClause ns (ImpossibleClause fc lhs)
        = do lhs' <- updateApp ns lhs
             pure (ImpossibleClause fc lhs')

    updateBody : List (Name, Name) -> ImpDecl FC -> Core FC (ImpDecl FC)
    updateBody ns (IDef fc n cs) 
        = do cs' <- traverse (updateClause ns) cs
             n' <- findMethName ns fc n
             pure (IDef fc n' cs')
    updateBody ns _ 
        = throw (GenericMsg fc 
                   "Implementation body can only contain definitions")
