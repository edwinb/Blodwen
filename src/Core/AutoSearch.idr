module Core.AutoSearch

-- Proof search for auto implicits and interface implementations

import Core.Context
import Core.TT
import Core.Normalise
import Core.Unify

import Data.List

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
-- TODO: Remove this, it's just a test...
searchType loc env (NPrimVal IntType)
    = pure (PrimVal (I 42))
searchType loc env ty 
    = do gam <- getCtxt
         try (trivial loc env (quote empty env ty))
          (throw (CantSolveGoal loc env (quote empty env ty)))

-- Given a name, which must currently be a hole, return an expression which 
-- would fit the hole by proof search.
export
search : {auto c : Ref Ctxt Defs} ->
         {auto u : Ref UST (UState annot)} ->
         annot -> Name -> Core annot ClosedTerm
search loc n_in
    = do gam <- getCtxt
         case lookupDefTyName n_in gam of
              [(n, def, ty)] =>
                   case def of
                        Hole locs False => searchType loc [] (nf gam [] ty)
                        _ => throw (InternalError "Not a hole")
              [] => throw (UndefinedName loc n_in)
              ns => throw (AmbiguousName loc (map fst ns))

