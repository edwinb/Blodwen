module TTImp.Generate

-- Attempt to generate a complete definition from a type

import Core.Context
import Core.Metadata
import Core.Normalise
import Core.TT
import Core.Unify

import TTImp.CaseSplit
import TTImp.ProcessDef
import TTImp.TTImp
import TTImp.Utils

mutual
  fnGenName : Bool -> GenName -> String
  fnGenName lhs (Nested _ n) = fnName lhs n
  fnGenName lhs (CaseBlock n _) = fnName lhs n
  fnGenName lhs (WithBlock n _) = fnName lhs n

  fnName : Bool -> Name -> String
  fnName lhs (UN n) 
      = if any (not . identChar) (unpack n)
           then if lhs then "(" ++ n ++ ")"
                       else "op"
           else n
  fnName lhs (NS _ n) = fnName lhs n
  fnName lhs (DN s _) = s
  fnName lhs (GN g) = fnGenName lhs g
  fnName lhs n = show n

getEnvArgNames : Defs -> Nat -> NF [] -> List String
getEnvArgNames defs Z sc = getArgNames defs [] [] sc
getEnvArgNames defs (S k) (NBind n _ sc)
    = getEnvArgNames defs k (sc (MkClosure defaultOpts [] [] Erased))
getEnvArgNames defs n ty = []

export
makeDef : {auto c : Ref Ctxt Defs} ->
          {auto m : Ref Meta (Metadata annot)} ->
          {auto u : Ref UST (UState annot)} ->
          (annot -> (Name, Nat, ClosedTerm) -> Bool) -> 
          Name -> Core annot (Maybe (annot, List (RawImp annot, RawImp annot)))
makeDef p n 
    = do Just (loc, n, envlen, ty) <- findTyDeclAt p
            | Nothing => pure Nothing
         defs <- get Ctxt
         let argns = getEnvArgNames defs envlen (nf defs [] ty)
         let rhshole = uniqueName defs [] (fnName False n ++ "_rhs")
         let initcs = (apply (IVar loc n) (map (IBindVar loc) argns),
                       IHole loc rhshole)
         pure (Just (loc, [initcs]))

