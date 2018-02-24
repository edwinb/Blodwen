module Core.AutoSearch

-- Proof search for auto implicits and interface implementations

import Core.Context
import Core.TT
import Core.CaseTree
import Core.Normalise
import Core.Unify

import Data.List

%default covering

trivial : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState annot)} ->
          annot -> Env Term vars -> Term vars -> Core annot (Term vars)
trivial loc [] ty = throw (CantSolveGoal loc [] ty)
trivial loc (b :: env) ty 
-- If the type of the variable at the top of the environment converts with
-- the goal, use it (converts, not unifying, so no solving metavariables here)
    = try (do gam <- get Ctxt
              let bty = binderType b
              if convert gam (b :: env) (weaken bty) ty
                 then pure (Local Here)
                 else throw (CantSolveGoal loc (b :: env) ty))
          (case shrinkTerm ty (DropCons SubRefl) of
                Nothing => throw (CantSolveGoal loc (b :: env) ty)
                Just ty' => do tm' <- trivial loc env ty'
                               pure (weaken tm'))

mkArgs : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST (UState annot)} ->
         annot -> Env Term vars -> Term vars -> 
         Core annot (List (Name, Term vars), Term vars)
mkArgs loc env (Bind n (Pi c info ty) sc)
    = do argName <- addHole loc env ty
         let arg = mkConstantApp argName env
         (rest, restTy) <- mkArgs loc env (subst arg sc)
         pure ((argName, arg) :: rest, restTy)
mkArgs loc env ty = pure ([], ty)

-- Search recursively, but only if the given name wasn't solved by unification
searchIfHole : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState annot)} ->
               annot -> Nat -> Name -> Core annot ()
searchIfHole loc Z n = throw (InternalError "Search depth limit reached")
searchIfHole loc (S depth) n
    = do gam <- get Ctxt
         case lookupDefExact n (gamma gam) of
              Nothing => throw (InternalError "Can't happen, name has mysteriously vanised")
              Just def =>
                   case def of
                        Hole locs False => do search loc depth n
                                              pure ()
                        _ => pure () -- Nothing to do

-- Apply the name to arguments and see if the result unifies with the target
-- type, then try to automatically solve any holes which were generated.
-- If there are any remaining holes, search fails.
searchName : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Nat -> Env Term vars -> NF vars -> Name -> Core annot (Term vars)
searchName loc depth env ty con
    = do gam <- get Ctxt
         case lookupDefTyExact con (gamma gam) of
              Just (DCon tag arity _, cty)
                  => do let nty = normalise gam [] cty
                        (args, appTy) <- mkArgs loc env (embed nty)
                        [] <- unify InTerm loc env ty (nf gam env appTy)
                              | _ => throw (CantSolveGoal loc env (quote (noGam gam) env ty))
                        let candidate = apply (Ref (DataCon tag arity) con)
                                              (map snd args)
                        -- TODO: Go through the arguments and solve them, if they
                        -- haven't been solved by unification
                        traverse (searchIfHole loc depth) (map fst args)
                        pure candidate
              _ => throw (CantSolveGoal loc env (quote (noGam gam) env ty))


searchNames : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              annot -> Nat -> Env Term vars -> NF vars -> List Name -> Core annot (Term vars)
searchNames loc depth env ty []
    = do gam <- get Ctxt
         throw (CantSolveGoal loc env (quote (noGam gam) env ty))
searchNames loc depth env ty (n :: ns)
    = do gam <- get Ctxt
         log 5 $ "Searching " ++ show n ++ " for " ++ show (quote (noGam gam) env ty)
         try (searchName loc depth env ty n)
             (searchNames loc depth env ty ns)

-- Type directed search - take the first thing of the given type it finds using
-- the current environment.
searchType : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Nat -> Env Term vars -> NF vars -> Core annot (Term vars)
searchType loc depth env (NBind n (Pi c info ty) scfn)
    = do xn <- genName "x"
         gam <- get Ctxt
         let env' : Env Term (n :: _) = Pi c info (quote (noGam gam) env ty) :: env
         let sc = scfn (toClosure False env (Ref Bound xn))
         let tmsc = refToLocal xn n (quote (noGam gam) env sc)
         scVal <- searchType loc depth env' (nf gam env' tmsc)
         pure (Bind n (Lam c info (quote (noGam gam) env ty)) scVal)
searchType loc depth env ty@(NTCon n t ar args)
    = do gam <- get Ctxt
         if length args == ar
           then do cons <- getHintsFor loc n
                   log 5 $ "Hints for " ++ show n ++ ": " ++ show cons
                   try (trivial loc env (quote (noGam gam) env ty))
                       (searchNames loc depth env ty cons)
           else throw (CantSolveGoal loc env (quote (noGam gam) env ty))
searchType loc depth env (NPrimVal IntType)
    = pure (PrimVal (I 0))
searchType loc depth env ty 
    = do gam <- get Ctxt
         try (trivial loc env (quote (noGam gam) env ty))
             (throw (CantSolveGoal loc env (quote (noGam gam) env ty)))

searchHole : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Nat -> Name -> Defs -> GlobalDef -> Core annot ClosedTerm
searchHole loc depth n gam glob
    = do let nty = nf gam [] (type glob)
         soln <- searchType loc depth [] nty
         addDef n (record { definition = PMDef True [] (STerm soln) } glob)
         removeHoleName n
         pure soln

-- Declared in Unify.idr (please remember to keep this type up to date!)
-- search : {auto c : Ref Ctxt Defs} ->
--          {auto u : Ref UST (UState annot)} ->
--          annot -> Nat -> Name -> Core annot ClosedTerm
Core.Unify.search loc depth n_in
    = do gam <- get Ctxt
         case lookupHoleName n_in (gamma gam) of
              Just (n, glob) =>
                   case definition glob of
                        Hole locs False => searchHole loc depth n gam glob
                        BySearch _ => searchHole loc depth n gam glob
                        _ => throw (InternalError "Not a hole")
              _ => throw (UndefinedName loc n_in)
  where
    lookupHoleName : Name -> Gamma -> Maybe (Name, GlobalDef)
    lookupHoleName n gam
        = case lookupGlobalExact n gam of
               Just res => Just (n, res)
               Nothing => case lookupGlobalName n gam of
                               [res] => Just res
                               _ => Nothing
