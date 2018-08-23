module Idris.Elab.Implementation

import Core.Binary
import Core.Context
import Core.Core
import Core.TT
import Core.Unify

import Idris.BindImplicits
import Idris.Elab.Utils
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

addDefaults : FC -> List Name -> List (Name, List (ImpClause FC)) ->
              List (ImpDecl FC) -> 
              (List (ImpDecl FC), List Name) -- Updated body, list of missing methods
addDefaults fc ms defs body
    = let missing = dropGot ms body in
          extendBody [] missing body
  where
    extendBody : List Name -> List Name -> List (ImpDecl FC) -> 
                 (List (ImpDecl FC), List Name)
    extendBody ms [] body = (body, ms)
    extendBody ms (n :: ns) body
        = case lookup n defs of
               Nothing => extendBody (n :: ms) ns body
               Just cs => extendBody ms ns (IDef fc n cs :: body)

    dropGot : List Name -> List (ImpDecl FC) -> List Name
    dropGot ms [] = ms
    dropGot ms (IDef _ n _ :: ds)
        = dropGot (filter (/= n) ms) ds
    dropGot ms (_ :: ds) = dropGot ms ds

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
-- TODO: Refactor all these steps into separate functions
elabImplementation {vars} fc vis env nest cons iname ps impln body_in
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

         let impsp = nub (concatMap findIBinds ps)

         log 1 $ "Found interface " ++ show cn ++ " : "
                 ++ show (normaliseHoles defs [] ity)
                 ++ " with params: " ++ show (params cdata)
                 ++ " and parents: " ++ show (parents cdata)
                 ++ " using implicits: " ++ show impsp
                 ++ " and methods: " ++ show (methods cdata) ++ "\n"
                 ++ "Constructor: " ++ show (iconstructor cdata)
         log 5 $ "Making implementation " ++ show impName

         -- 0. Lookup default definitions and add them to to body
         let (body, missing)
               = addDefaults fc (map (dropNS . fst) (methods cdata)) 
                                (defaults cdata) body_in

         log 5 $ "Added defaults: body is " ++ show body
         log 5 $ "Missing methods: " ++ show missing

         -- 1. Build the type for the implementation
         -- Make the constraints auto implicit arguments, which can be explicitly
         -- given when using named implementations
         --    (cs : Constraints) -> Impl params
         -- Don't make it a hint if it's a named implementation
         let opts = maybe [Inline, Hint True] (const [Inline]) impln

         let impTy = bindTypeNames vars $
                     bindConstraints fc AutoImplicit cons 
                         (apply (IVar fc iname) ps)
         let impTyDecl = IClaim fc vis opts (MkImpTy fc impName impTy)
         log 5 $ "Implementation type: " ++ show impTy
         processDecl env nest impTyDecl

         -- 2. Elaborate top level function types for this interface
         defs <- get Ctxt
         fns <- traverse (topMethType impName impsp (params cdata)
                                      (map fst (methods cdata))) 
                         (methods cdata)
         traverse (processDecl env nest) (map mkTopMethDecl fns)

         -- 3. Build the record for the implementation
         let mtops = map (Basics.fst . snd) fns
         let con = iconstructor cdata
         let ilhs = impsApply (IVar fc impName) 
                              (map (\x => (UN x, IBindVar fc x)) impsp)
         -- RHS is the constructor applied to a search for the necessary
         -- parent constraints, then the method implementations
         let irhs = apply (IVar fc con)
                          (map (const (ISearch fc 500)) (parents cdata)
                           ++ map (mkMethField impsp) (map Basics.snd fns))
         let impFn = IDef fc impName [PatClause fc ilhs irhs]
         log 5 $ "Implementation record: " ++ show impFn
         traverse (processDecl env nest) [impFn]

         -- 4. (TODO: Order method bodies to be in declaration order, in
         --    case of dependencies)

         -- 5. Elaborate the method bodies

         -- If it's a named implementation, add it as a global hint while
         -- elaborating the bodies
         defs <- get Ctxt
         let hs = openHints defs
         maybe (pure ()) (\x => addOpenHint impName) impln

         body' <- traverse (updateBody (map methNameUpdate fns)) body
         log 10 $ "Implementation body: " ++ show body'
         traverse (processDecl env nest) body'
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

    impsApply : RawImp FC -> List (Name, RawImp FC) -> RawImp FC
    impsApply fn [] = fn
    impsApply fn ((n, arg) :: ns) 
        = impsApply (IImplicitApp fc fn (Just n) arg) ns

    mkLam : List Name -> RawImp FC -> RawImp FC
    mkLam [] tm = tm
    mkLam (x :: xs) tm = ILam fc RigW Explicit (Just x) (Implicit fc) (mkLam xs tm)

    -- When applying the method in the field for the record, eta expand
    -- the explicit arguments so that implicits get inserted in the right 
    -- place
    mkMethField : List String -> (Name, RawImp FC) -> RawImp FC
    mkMethField impsp (n, ty) 
        = let argns = getExplicitArgs 0 ty 
              imps = nub (filter (\n => n `elem` impsp) (findIBinds ty)) in
              -- Pass through implicit arguments to the function which are also
              -- implicit arguments to the declaration
              mkLam argns 
                    (impsApply 
                         (apply (IVar fc n) (map (IVar fc) argns))
                         (map (\n => (UN n, IVar fc (UN n))) imps))

    methName : Name -> Name
    methName (NS _ n) = methName n
    methName n = MN (show n ++ "_" ++ show iname ++ "_" ++
                     maybe "" show impln ++ "_" ++
                     showSep "_" (map show ps)) 0
    
    applyCon : Name -> Name -> Core FC (Name, RawImp FC)
    applyCon impl n = do mn <- inCurrentNS (methName n)
                         pure (dropNS n, IVar fc mn)
    
    topMethType : Name -> List String -> List Name -> List Name ->
                  (Name, RawImp FC) -> 
                  Core FC (Name, Name, RawImp FC)
    topMethType impName impsp pnames allmeths (mn, mty_in)
        = do -- Get the specialised type by applying the method to the
             -- parameters
             n <- inCurrentNS (methName mn)

             -- Avoid any name clashes between parameters and method types by
             -- renaming IBindVars in the method types which appear in the
             -- paramaters
             let mty_in = substNames vars !(traverse (applyCon impName) allmeths) mty_in
             let mty_in = renameIBinds impsp (findIBinds mty_in) mty_in
             let mbase = bindConstraints fc AutoImplicit cons $
                         substNames vars (zip pnames ps) mty_in
             let ibound = findIBinds mbase

             let mty = bindTypeNamesUsed ibound vars mbase

             log 3 $ "Method " ++ show mn ++ " ==> " ++
                     show n ++ " : " ++ show mty
             log 5 $ "From " ++ show mbase 
             log 3 $ "Param names: " ++ show pnames 
             log 10 $ "Used names " ++ show ibound
             pure (mn, n, mty)
             
    mkTopMethDecl : (Name, Name, RawImp FC) -> ImpDecl FC
    mkTopMethDecl (mn, n, mty) = IClaim fc vis [] (MkImpTy fc n mty)

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
