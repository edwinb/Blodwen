module TTImp.MakeLemma

import Core.Context
import Core.Metadata
import Core.Normalise
import Core.TT

import TTImp.Elab.Unelab
import TTImp.TTImp
import TTImp.Utils

import Data.List

%default covering

used : RigCount -> Bool
used Rig0 = False
used _ = True

-- True if the variable appears guarded by a constructor in the term
bindable : Elem x vars -> Term vars -> Bool
bindable {x} p tm
    = case getFnArgs tm of
           (Ref (TyCon _ _) n, args) => any (bindable p) args
           (Ref (DataCon _ _) _, args) => any (bindable p) args
           (Local _ p', []) => sameVar p p'
           _ => False

bindableArg : Elem x vars -> Term vars -> Bool
bindableArg p (Bind _ (Pi _ _ ty) sc)
   = bindable p ty || bindableArg (There p) sc
bindableArg p _ = False

getArgs : {auto c : Ref Ctxt Defs} ->
          annot -> Env Term vars -> Term vars -> 
          Core annot (List (Name, Maybe Name, PiInfo, RigCount, RawImp annot), RawImp annot)
getArgs {vars} loc env (Bind x (Pi c p ty) sc)
    = do ty' <- unelab loc env ty
         defs <- get Ctxt
         let x' = UN (uniqueName defs (map nameRoot vars) (nameRoot x))
         (sc', ty) <- getArgs loc (Pi c p ty :: env) (renameTop x' sc)
         -- Don't need to use the name if it's not used in the scope type
         let mn = case c of
                       RigW => case shrinkTerm sc (DropCons SubRefl) of
                                    Nothing => Just x'
                                    _ => Nothing
                       _ => Just x'
         let p' = if used c && not (bindableArg Here sc)
                     then Explicit
                     else Implicit
         pure ((x, mn, p', c, ty') :: sc', ty)
getArgs loc env ty
      = do ty' <- unelab loc env ty
           pure ([], ty')

mkType : annot -> List (Name, Maybe Name, PiInfo, RigCount, RawImp annot) -> 
         RawImp annot -> RawImp annot
mkType loc [] ret = ret
mkType loc ((_, n, p, c, ty) :: rest) ret
    = IPi loc c p n ty (mkType loc rest ret)

mkApp : annot -> Name ->
        List (Name, Maybe Name, PiInfo, RigCount, RawImp annot) -> RawImp annot
mkApp loc n args
    = apply (IVar loc n) (mapMaybe getArg args)
  where
    getArg : (Name, Maybe Name, PiInfo, RigCount, RawImp annot) -> Maybe (RawImp annot)
    getArg (x, _, Explicit, _, _) = Just (IVar loc x)
    getArg _ = Nothing

-- Return a top level type for the lemma, and an expression which applies
-- the lemma to solve a hole with 'locs' arguments
export
makeLemma : {auto m : Ref Meta (Metadata annot)} ->
            {auto c : Ref Ctxt Defs} ->
            annot -> Name -> Nat -> ClosedTerm -> 
            Core annot (RawImp annot, RawImp annot)
makeLemma loc n nlocs ty
    = do (args, ret) <- getArgs loc [] ty
         pure (mkType loc args ret, mkApp loc n args)

