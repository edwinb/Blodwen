module Core.AutoSearch

-- Proof search for auto implicits and interface implementations

import Core.Context
import Core.TT
import Core.CaseTree
import Core.Normalise
import Core.Unify

import Data.List

%default covering

-- Given a name, which must currently be a hole, attempt to fill in the hole with
-- an expression which would fit. Also returns the expression.
-- (Defined later; we need this when searching arguments recursively too)
export
search : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST (UState annot)} ->
         annot -> Name -> Core annot ClosedTerm

-- try one search strategy; if it fails, try another
try : {auto c : Ref Ctxt Defs} -> {auto e : Ref UST (UState annot)} ->
      Core annot a -> Core annot a -> Core annot a
try elab1 elab2
    = do ctxt <- get Ctxt
         ust <- get UST
         catch elab1
               (\err => do put Ctxt ctxt
                           put UST ust
                           elab2)

trivial : {auto c : Ref Ctxt Defs} ->
          {auto u : Ref UST (UState annot)} ->
          annot -> Env Term vars -> Term vars -> Core annot (Term vars)
trivial loc [] ty = throw (CantSolveGoal loc [] ty)
trivial loc (b :: env) ty 
-- If the type of the variable at the top of the environment converts with
-- the goal, use it (converts, not unifying, so no solving metavariables here)
    = try (do gam <- getCtxt
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
         Env Term vars -> Term vars -> 
         Core annot (List (Name, Term vars), Term vars)
mkArgs env (Bind n (Pi info ty) sc)
    = do argName <- addHole env ty
         let arg = mkConstantApp argName env
         (rest, restTy) <- mkArgs env (subst arg sc)
         pure ((argName, arg) :: rest, restTy)
mkArgs env ty = pure ([], ty)

-- Search recursively, but only if the given name wasn't solved by unification
searchIfHole : {auto c : Ref Ctxt Defs} ->
               {auto u : Ref UST (UState annot)} ->
               annot -> Name -> Core annot ()
searchIfHole loc n
    = do gam <- getCtxt
         case lookupDefExact n gam of
              Nothing => throw (InternalError "Can't happen, name has mysteriously vanised")
              Just def =>
                   case def of
                        Hole locs False => do search loc n
                                              pure ()
                        _ => pure () -- Nothing to do

-- Apply the name to arguments and see if the result unifies with the target
-- type, then try to automatically solve any holes which were generated.
-- If there are any remaining holes, search fails.
searchName : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Env Term vars -> NF vars -> Name -> Core annot (Term vars)
searchName loc env ty con
    = do gam <- getCtxt
         case lookupDefTyExact con gam of
              Just (DCon tag arity, cty)
                  => do let nty = normalise gam [] cty
                        (args, appTy) <- mkArgs env (embed nty)
                        solveConstraints InTerm
                        [] <- unify InTerm loc env ty (nf gam env appTy)
                              | _ => throw (CantSolveGoal loc env (quote empty env ty))
                        solveConstraints InTerm
                        let candidate = apply (Ref (DataCon tag arity) con)
                                              (map snd args)
                        -- TODO: Go through the arguments and solve them, if they
                        -- haven't been solved by unification
                        traverse (searchIfHole loc) (map fst args)
                        pure candidate
              _ => throw (CantSolveGoal loc env (quote empty env ty))


searchNames : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              annot -> Env Term vars -> NF vars -> List Name -> Core annot (Term vars)
searchNames loc env ty []
    = throw (CantSolveGoal loc env (quote empty env ty))
searchNames loc env ty (n :: ns)
    = do log 0 $ "Searching " ++ show n ++ " for " ++ show (quote empty env ty)
         try (searchName loc env ty n)
             (searchNames loc env ty ns)

-- Type directed search - take the first thing of the given type it finds using
-- the current environment.
searchType : {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             annot -> Env Term vars -> NF vars -> Core annot (Term vars)
searchType loc env (NBind n (Pi info ty) scfn)
    = do xn <- genName "x"
         gam <- getCtxt
         let env' : Env Term (n :: _) = Pi info (quote empty env ty) :: env
         let sc = scfn (toClosure False env (Ref Bound xn))
         let tmsc = refToLocal xn n (quote empty env sc)
         scVal <- searchType loc env' (nf gam env' tmsc)
         pure (Bind n (Lam info (quote empty env ty)) scVal)
searchType loc env ty@(NTCon n t ar args)
    = if length args == ar
         then do gam <- getCtxt
                 case lookupDefExact n gam of
                      Just (TCon _ _ cons) => searchNames loc env ty cons
                      _ => throw (CantSolveGoal loc env (quote empty env ty))
         else throw (CantSolveGoal loc env (quote empty env ty))
-- TODO: Remove this, it's just a test...
searchType loc env (NPrimVal IntType)
    = pure (PrimVal (I 42))
searchType loc env ty 
    = do gam <- getCtxt
         try (trivial loc env (quote empty env ty))
          (throw (CantSolveGoal loc env (quote empty env ty)))

-- Type at top of file (please remember to keep this up to date!)
-- search : {auto c : Ref Ctxt Defs} ->
--          {auto u : Ref UST (UState annot)} ->
--          annot -> Name -> Core annot ClosedTerm
search loc n_in
    = do gam <- getCtxt
         case lookupHoleName n_in gam of
              Just (n, glob) =>
                   case definition glob of
                        Hole locs False => 
                             do let nty = nf gam [] (type glob)
                                soln <- searchType loc [] nty
                                addDef n (record { definition = PMDef True [] 
                                                                   (STerm soln) } glob)
                                removeHoleName n
                                pure soln
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
