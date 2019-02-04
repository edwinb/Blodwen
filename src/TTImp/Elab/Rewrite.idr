module TTImp.Elab.Rewrite

import Core.Context
import Core.GetType
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
                  Core annot (NF vars, NF vars, NF vars)
getRewriteTerms loc defs (NTCon eq t a args) err
    = if isEqualTy eq defs
         then case reverse args of
                   (rhs :: lhs :: rhsty :: lhsty :: _) =>
                        pure (evalClosure defs lhs, 
                              evalClosure defs rhs,
                              evalClosure defs lhsty)
                   _ => throw err
         else throw err
getRewriteTerms loc defs ty err
    = throw err

-- Returns the rewriting lemma to use, and the predicate for passing to the
-- rewriting lemma
export
elabRewrite : {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} -> 
              annot -> Env Term vars ->
              (expected : Term vars) -> 
              (rulety : Term vars) ->
              Core annot (Name, Term vars, Term vars)
elabRewrite loc env expected rulety
    = do defs <- get Ctxt
         parg <- genVarName "rwarg"
         let tynf = nf defs env rulety
         (lt, rt, lty) <- getRewriteTerms loc defs tynf (NotRewriteRule loc env rulety)
         lemn <- findRewriteLemma loc rulety

         let rwexp_sc = replace defs env lt (Ref Bound parg) (nf defs env expected)
         let pred = Bind parg (Lam RigW Explicit (quote (noGam defs) env lty))
                          (refToLocal (Just RigW) parg parg rwexp_sc)
         predty <- getType loc env pred

         -- if the rewritten expected type converts with the original,
         -- then the rewrite did nothing, which is an error
         log 5 $ "Rewrite data: " ++ show pred ++ " : " ++ show predty ++
                   "\n\tReplacing " ++ show (quote defs env lt) ++ " gives " ++ show rwexp_sc ++ " for " ++ show expected
         when (convert defs env rwexp_sc expected) $
             throw (RewriteNoChange loc env rulety expected)
         pure (lemn, pred, predty)
