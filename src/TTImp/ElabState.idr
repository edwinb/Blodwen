module TTImp.ElabState

import TTImp.TTImp
import Core.CaseTree
import Core.Context
import Core.TT
import Core.Normalise
import Core.Unify

import Data.List

-- How the elaborator should deal with IBindVar:
-- * NONE: IBindVar is not valid (rhs of an definition, top level expression)
-- * PI True: Bind implicits as Pi, in the appropriate scope, and bind
--            any additional holes
-- * PI False: As above, but don't bind additional holes
-- * PATTERN: Bind implicits as PVar, but only at the top level
public export
data ImplicitMode = NONE | PI Bool | PATTERN

public export
data ElabMode = InType | InLHS | InExpr

public export
record EState (vars : List Name) where
  constructor MkElabState
  boundNames : List (Name, (Term vars, Term vars))
                  -- implicit pattern/type variable bindings and the 
                  -- term/type they elaborated to
  toBind : List (Name, (Term vars, Term vars))
                  -- implicit pattern/type variables which haven't been
                  -- bound yet.
  defining : Name -- Name of thing we're currently defining

public export
Elaborator : Type -> Type
Elaborator annot
    = {vars : List Name} ->
      Ref Ctxt Defs -> Ref UST (UState annot) ->
      Ref ImpST (ImpState annot) ->
      Env Term vars -> NestedNames vars -> 
      ImpDecl annot -> Core annot ()


-- A label for the internal elaborator state
export
data EST : Type where

export
initEState : Name -> EState vars
initEState n = MkElabState [] [] n

export
weakenedEState : {auto e : Ref EST (EState vs)} ->
                 Core annot (Ref EST (EState (n :: vs)))
weakenedEState
    = do est <- get EST
         e' <- newRef EST (MkElabState (map wknTms (boundNames est))
                                       (map wknTms (toBind est))
                                       (defining est))
         pure e'
  where
    wknTms : (Name, (Term vs, Term vs)) -> 
             (Name, (Term (n :: vs), Term (n :: vs)))
    wknTms (f, (x, y)) = (f, (weaken x, weaken y))

-- remove the outermost variable from the unbound implicits which have not
-- yet been bound. If it turns out to depend on it, that means it can't
-- be bound at the top level, which is an error.
export
strengthenedEState : {auto e : Ref EST (EState (n :: vs))} ->
                     (top : Bool) -> annot ->
                     Core annot (EState vs)
strengthenedEState True loc = do est <- get EST
                                 pure (initEState (defining est))
strengthenedEState False loc 
    = do est <- get EST
         bns <- traverse strTms (boundNames est)
         todo <- traverse strTms (toBind est)
         pure (MkElabState bns todo (defining est))
  where
    -- Remove any instance of the top level local variable from an
    -- application. Fail if it turns out to be necessary.
    -- NOTE: While this isn't strictly correct given the type of the hole
    -- which stands for the unbound implicits, it's harmless because we
    -- never actualy *use* that hole - this process is only to ensure that the
    -- unbound implicit doesn't depend on any variables it doesn't have
    -- in scope.
    removeArgVars : List (Term (n :: vs)) -> Maybe (List (Term vs))
    removeArgVars [] = pure []
    removeArgVars (Local (There p) :: args) 
        = do args' <- removeArgVars args
             pure (Local p :: args')
    removeArgVars (Local Here :: args) 
        = removeArgVars args
    removeArgVars (a :: args)
        = do a' <- shrinkTerm a (DropCons SubRefl)
             args' <- removeArgVars args
             pure (a' :: args')

    removeArg : Term (n :: vs) -> Maybe (Term vs)
    removeArg tm with (unapply tm)
      removeArg (apply f args) | ArgsList 
          = do args' <- removeArgVars args
               f' <- shrinkTerm f (DropCons SubRefl)
               pure (apply f' args')

    strTms : (Name, (Term (n :: vs), Term (n :: vs))) -> 
             Core annot (Name, (Term vs, Term vs))
    strTms {vs} (f, (x, y))
        = case (removeArg x, shrinkTerm y (DropCons SubRefl)) of
               (Just x', Just y') => pure (f, (x', y'))
               _ => throw (GenericMsg loc ("Invalid unbound implicit " ++ show f))

export
clearEState : {auto e : Ref EST (EState vs)} ->
              Core annot ()
clearEState = do est <- get EST
                 put EST (initEState (defining est))

export
clearToBind : {auto e : Ref EST (EState vs)} ->
              Core annot ()
clearToBind
    = do est <- get EST
         put EST (record { toBind = [] } est)
  
export
dropTmIn : List (a, (c, d)) -> List (a, d)
dropTmIn = map (\ (n, (_, t)) => (n, t))

-- Bind implicit arguments, returning the new term and its updated type
bindImplVars : Int -> 
               ImplicitMode ->
               Gamma ->
               List (Name, Term vars) ->
               Term vars -> Term vars -> (Term vars, Term vars)
bindImplVars i NONE gam args scope scty = (scope, scty)
bindImplVars i mode gam [] scope scty = (scope, scty)
bindImplVars i mode gam ((n, ty) :: imps) scope scty
    = let (scope', ty') = bindImplVars (i + 1) mode gam imps scope scty
          tmpN = MN "unb" i
          repNameTm = repName (Ref Bound tmpN) scope' 
          repNameTy = repName (Ref Bound tmpN) ty' in
          case mode of
               PATTERN =>
                  case lookupDefExact n gam of
                       Just (PMDef _ _ t) =>
                          (Bind n (PLet (embed (normalise gam [] (Ref Func n))) ty) 
                                      (refToLocal tmpN n repNameTm), 
                           Bind n (PLet (embed (normalise gam [] (Ref Func n))) ty) 
                                      (refToLocal tmpN n repNameTy))
                       _ =>
                          (Bind n (PVar ty) (refToLocal tmpN n repNameTm), 
                           Bind n (PVTy ty) (refToLocal tmpN n repNameTy))
               _ => (Bind n (Pi Implicit ty) (refToLocal tmpN n repNameTm), ty')
  where
    -- Replace the name applied to the given number of arguments 
    -- with another term
    repName : (new : Term vars) -> Term vars -> Term vars
    repName new (Local p) = Local p
    repName new (Ref nt fn)
        = case nameEq n fn of
               Nothing => Ref nt fn
               Just Refl => new
    repName new (Bind y b tm) 
        = Bind y (assert_total (map (repName new) b)) 
                 (repName (weaken new) tm)
    repName new (App fn arg) 
        = case getFn fn of
               Ref nt fn' =>
                   case nameEq n fn' of
                        Nothing => App (repName new fn) (repName new arg)
                        Just Refl => 
                           let locs = case lookupDefExact fn' gam of
                                           Just (Hole i _) => i
                                           _ => 0
                                        in
                               apply new (drop locs (getArgs (App fn arg)))
               _ => App (repName new fn) (repName new arg)
    repName new (PrimVal y) = PrimVal y
    repName new Erased = Erased
    repName new TType = TType

export
bindImplicits : ImplicitMode ->
                Gamma -> Env Term vars ->
                List (Name, Term vars) ->
                Term vars -> Term vars -> (Term vars, Term vars)
bindImplicits {vars} mode gam env hs tm ty 
   = bindImplVars 0 mode gam (map nHoles hs)
                             (normaliseHoles gam env tm)
                             (normaliseHoles gam env ty)
  where
    nHoles : (Name, Term vars) -> (Name, Term vars)
    nHoles (n, ty) = (n, normaliseHoles gam env ty)

export
bindTopImplicits : ImplicitMode -> Gamma -> Env Term vars ->
                   List (Name, ClosedTerm) -> Term vars -> Term vars ->
                   (Term vars, Term vars)
bindTopImplicits {vars} mode gam env hs tm ty
    = bindImplicits mode gam env (map weakenVars hs) tm ty
  where
    weakenVars : (Name, ClosedTerm) -> (Name, Term vars)
    weakenVars (n, tm) = (n, rewrite sym (appendNilRightNeutral vars) in
                                     weakenNs vars tm)

-- Find any holes in the resulting expression, and implicitly bind them
-- at the top level (i.e. they can't depend on any explicitly given
-- arguments).
-- Return the updated term and type, and the names of holes which occur
export
findHoles : {auto c : Ref Ctxt Defs} -> {auto u : Ref UST (UState annot)} ->
            ImplicitMode -> Env Term vars -> Term vars -> Term vars ->
            Core annot (Term vars, Term vars, List Name) 
findHoles NONE env tm exp = pure (tm, exp, [])
findHoles (PI False) env tm exp = pure (tm, exp, [])
findHoles mode env tm exp
    = do h <- newRef HVar []
         tm <- holes h tm
         hs <- get HVar
         gam <- getCtxt
         log 5 $ "Extra implicits to bind: " ++ show (reverse hs)
         let (tm', ty) = bindTopImplicits mode gam env (reverse hs) tm exp
         traverse implicitBind (map fst hs)
         pure (tm', ty, map fst hs)
  where
    data HVar : Type where -- empty type to label the local state

    mkType : (vars : List Name) -> Term hs -> Maybe (Term hs)
    mkType (v :: vs) (Bind tm (Pi _ ty) sc) 
        = do sc' <- mkType vs sc
             shrinkTerm sc' (DropCons SubRefl)
    mkType _ tm = pure tm

    processHole : Ref HVar (List (Name, ClosedTerm)) ->
                  Name -> (vars : List Name) -> ClosedTerm ->
                  Core annot ()
    processHole h n vars ty
       = do hs <- get HVar
--             putStrLn $ "IMPLICIT: " ++ show (n, vars, ty)
            case mkType vars ty of
                 Nothing => pure ()
                 Just impTy =>
                    case lookup n hs of
                         Just _ => pure ()
                         Nothing => put HVar ((n, impTy) :: hs)

    holes : Ref HVar (List (Name, ClosedTerm)) ->
            Term vars -> 
            Core annot (Term vars)
    holes h {vars} (Ref nt fn) 
        = do gam <- getCtxt
             case lookupDefTyExact fn gam of
                  Just (Hole _ _, ty) =>
                       do processHole h fn vars ty
                          pure (Ref nt fn)
                  _ => pure (Ref nt fn)
    holes h (App fn arg)
        = do fn' <- holes h fn
             arg' <- holes h arg
             pure (App fn' arg')
    -- Allow implicits under 'Pi', 'PVar', 'PLet' only
    holes h (Bind y (Pi imp ty) sc)
        = do ty' <- holes h ty
             sc' <- holes h sc
             pure (Bind y (Pi imp ty') sc')
    holes h (Bind y (PVar ty) sc)
        = do ty' <- holes h ty
             sc' <- holes h sc
             pure (Bind y (PVar ty') sc')
    holes h (Bind y (PLet val ty) sc)
        = do val' <- holes h val
             ty' <- holes h ty
             sc' <- holes h sc
             pure (Bind y (PLet val' ty') sc')
    holes h tm = pure tm

export
renameImplicits : Gamma -> Term vars -> Term vars
renameImplicits gam (Bind (PV n) b sc) 
    = case lookupDefExact (PV n) gam of
           Just (PMDef _ _ def) =>
--                 trace ("OOPS " ++ show n ++ " = " ++ show def) $
                    Bind (UN n) b (renameImplicits gam (renameTop (UN n) sc))
           _ => Bind (UN n) b (renameImplicits gam (renameTop (UN n) sc))
renameImplicits gam (Bind n b sc) 
    = Bind n b (renameImplicits gam sc)
renameImplicits gam t = t

