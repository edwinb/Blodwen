module TTImp.Elab.Rewrite

import Core.Context
import Core.Normalise
import Core.TT
import Core.Unify

-- TODO: Later, we'll get the name of the lemma from the type, if it's one
-- that's generated for a dependent type. For now, always return the default
findRewriteLemma : {auto c : Ref Ctxt Defs} -> 
                   annot -> (rulety : Term vars) ->
                   Core annot Name
findRewriteLemma loc rulety
   = do defs <- get Ctxt
        case getRewrite defs of
             Nothing => throw (GenericMsg loc "No rewrite lemma defined")
             Just n => pure n

getRewriteTerms : annot -> Defs -> NF vars -> Error annot ->
                  Core annot (NF vars, NF vars)
getRewriteTerms loc defs (NTCon eq t a args) err
    = if isEqualTy eq defs
         then case reverse args of
                   (rhs :: lhs :: _) =>
                        pure (evalClosure defs lhs, evalClosure defs rhs)
                   _ => throw err
         else throw err
getRewriteTerms loc defs ty err
    = throw err

replace : Int -> Defs -> Env Term vars ->
          (lhs : NF vars) -> (parg : Name) -> (exp : NF vars) ->
          Term vars
replace {vars} tmpi defs env lhs parg tm
    = if convert defs env lhs tm
         then Ref Bound parg
         else repSub tm
  where
    repSub : NF vars -> Term vars
    repSub (NBind x b scfn)
       = let b' = map repSub b 
             x' = MN "tmp" tmpi
             sc' = replace (tmpi + 1) defs env lhs parg 
                           (scfn (toClosure defaultOpts env (Ref Bound x'))) in
             Bind x b' (refToLocal (Just (multiplicity b)) x' x sc')
    repSub (NApp hd args) 
       = apply (quote (noGam defs) env (NApp hd []))
                (map (replace tmpi defs env lhs parg) 
                     (map (evalClosure defs) args))
    repSub (NDCon n t a args)
       = apply (quote (noGam defs) env (NDCon n t a []))
                (map (replace tmpi defs env lhs parg) 
                     (map (evalClosure defs) args))
    repSub (NTCon n t a args)
       = apply (quote (noGam defs) env (NTCon n t a []))
                (map (replace tmpi defs env lhs parg) 
                     (map (evalClosure defs) args))
    repSub tm = quote (noGam defs) env tm

-- Returns the rewriting lemma to use, and the predicate for passing to the
-- rewriting lemma
export
elabRewrite : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} -> 
              annot -> Env Term vars ->
              (expected : Term vars) -> 
              (rulety : Term vars) ->
              Core annot (Name, Term vars)
elabRewrite loc env expected rulety
    = do defs <- get Ctxt
         parg <- genVarName "rwarg"
         let tynf = nf defs env rulety
         (lt, rt) <- getRewriteTerms loc defs tynf (NotRewriteRule loc env rulety)
         lemn <- findRewriteLemma loc rulety

         let rwexp_sc = replace 0 defs env lt parg (nf defs env expected)
         let pred = Bind parg (Lam RigW Explicit Erased)
                          (refToLocal (Just RigW) parg parg rwexp_sc)

         -- if the rewritten expected type converts with the original,
         -- then the rewrite did nothing, which is an error
         when (convert defs env rwexp_sc expected) $
             throw (RewriteNoChange loc env rulety expected)
         pure (lemn, pred)
