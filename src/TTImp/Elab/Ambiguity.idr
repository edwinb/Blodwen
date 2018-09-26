module TTImp.Elab.Ambiguity

import TTImp.TTImp
import TTImp.Elab.State

import Core.Context
import Core.Normalise
import Core.TT

import Data.List

%default covering

export
expandAmbigName : ElabMode -> EState vars -> 
                  Defs -> Env Term vars -> NestedNames vars ->
                  RawImp annot -> 
                  List (annot, Maybe (Maybe Name), RawImp annot) -> 
                  RawImp annot -> 
                  ExpType (Term vars) -> RawImp annot
-- Insert implicit dots here, for things we can't match on directly
-- (Only when mode is InLHS and it's not the name of the function we're 
-- defining)
expandAmbigName InLHS estate defs env nest orig args (IPrimVal fc c) exp
    = if isType c
         then IMustUnify fc "Primitive type constructor" orig
         else orig
  where
    isType : Constant -> Bool
    isType IntType = True
    isType IntegerType = True
    isType StringType = True
    isType CharType = True
    isType DoubleType = True
    isType WorldType = True
    isType _ = False
expandAmbigName InLHS estate defs env nest orig args (IBindVar fc n) exp
   = if n `elem` lhsPatVars estate
        then IMustUnify fc "Non linear pattern variable" orig
        else orig
expandAmbigName mode estate defs env nest orig args (IVar fc x) exp
   = case lookup x (names nest) of
          Just _ => orig
          Nothing => 
            case defined x env of
                 Just _ => if isNil args || notLHS mode 
                              then orig
                              else IMustUnify fc "Name applied to arguments" orig
                 Nothing => 
                    case lookupGlobalNameIn (currentNS defs) x 
                                            (gamma defs) of
                       [] => orig
                       [(n, gdef)] => mkTerm n gdef
                       ns => IAlternative fc Unique 
                                 (map (\t => mkTerm (fst t) (snd t)) ns)
  where
    buildAlt : RawImp annot -> 
               List (annot, Maybe (Maybe Name), RawImp annot) -> 
               RawImp annot
    buildAlt f [] = f
    buildAlt f ((loc', Nothing, a) :: as) 
        = buildAlt (IApp loc' f a) as
    buildAlt f ((loc', Just i, a) :: as) 
        = buildAlt (IImplicitApp loc' f i a) as
      
    isPrimAppF : (Defs -> Maybe Name) -> Name -> RawImp annot -> Bool
    isPrimAppF pname n (IPrimVal _ _)
        = case pname defs of
               Nothing => False
               Just n' => dropNS n == n'
    isPrimAppF pname _ _ = False

    isPrimApp : Name -> RawImp annot -> Bool
    isPrimApp fn arg
        = isPrimAppF fromIntegerName fn arg
        || isPrimAppF fromStringName fn arg
        || isPrimAppF fromCharName fn arg

    -- If it's not a constructor application, dot it
    wrapDot : ElabMode -> Name -> List (RawImp annot) -> 
              Def -> RawImp annot -> RawImp annot
    wrapDot _ _ _ (DCon _ _ _) tm = tm
    wrapDot InLHS n' [arg] _ tm 
       = if n' == defining estate || isPrimApp n' arg
            then tm
            else IMustUnify fc "Not a constructor application or primitive" tm
    wrapDot InLHS n' _ _ tm 
       = if n' == defining estate
            then tm
            else IMustUnify fc "Not a constructor application or primitive" tm
    wrapDot _ _ _ _ tm = tm

    mkTerm : Name -> GlobalDef -> RawImp annot
    mkTerm n def = wrapDot mode n (map (snd . snd) args)
                           (definition def) (buildAlt (IVar fc n) args)

    notLHS : ElabMode -> Bool
    notLHS InLHS = False
    notLHS _ = True

expandAmbigName mode estate defs env nest orig args (IApp fc f a) exp
   = expandAmbigName mode estate defs env nest orig 
                     ((fc, Nothing, a) :: args) f exp
expandAmbigName mode estate defs env nest orig args (IImplicitApp fc f n a) exp
   = expandAmbigName mode estate defs env nest orig 
                     ((fc, Just n, a) :: args) f exp
expandAmbigName mode estate defs env nest orig args _ _ = orig

stripDelay : Defs -> NF vars -> NF vars
stripDelay defs ty@(NTCon n t a args)
    = if isDelayType n defs
         then case reverse args of
                   [] => ty
                   (t :: _) => evalClosure defs t
         else ty
stripDelay defs tm = tm

mutual
  mightMatchD : Defs -> NF vars -> NF [] -> Bool
  mightMatchD defs l r = mightMatch defs (stripDelay defs l) (stripDelay defs r)

  mightMatch : Defs -> NF vars -> NF [] -> Bool
  mightMatch defs target (NBind n (Pi _ _ _) sc)
      = mightMatchD defs target (sc (toClosure defaultOpts [] Erased))
  mightMatch defs (NTCon n t a args) (NTCon n' t' a' args')
      = if n == n'
           then and (map Delay
                         (zipWith (mightMatchD defs) (map (evalClosure defs) args) 
                                                     (map (evalClosure defs) args')))
           else False
  mightMatch defs (NDCon n t a args) (NDCon n' t' a' args')
      = if t == t'
           then and (map Delay
                         (zipWith (mightMatchD defs) (map (evalClosure defs) args) 
                                                     (map (evalClosure defs) args')))
           else False
  mightMatch defs (NPrimVal x) (NPrimVal y) = x == y
  mightMatch defs NType NType = True
  mightMatch defs (NApp _ _) _ = True
  mightMatch defs NErased _ = True
  mightMatch defs _ (NApp _ _) = True
  mightMatch defs _ NErased = True
  mightMatch _ _ _ = False

-- Return true if the given name could return something of the given target type
couldBeName : Defs -> NF vars -> Name -> Bool
couldBeName defs target n
    = case lookupTyExact n (gamma defs) of
           Nothing => True -- could be a local name, don't rule it out
           Just ty => mightMatchD defs target (nf defs [] ty)

couldBeFn : Defs -> NF vars -> RawImp annot -> Bool
couldBeFn defs ty (IVar _ n) = couldBeName defs ty n
couldBeFn defs ty _ = True

couldBe : Defs -> NF vars -> RawImp annot -> Bool
couldBe {vars} defs ty@(NTCon n _ _ _) app = couldBeFn {vars} defs ty (getFn app)
couldBe {vars} defs ty@(NPrimVal _) app = couldBeFn {vars} defs ty (getFn app)
couldBe defs ty _ = True -- target is not a concrete type, so could be possible

export
pruneByType : Defs -> NF vars -> List (RawImp annot) -> List (RawImp annot)
pruneByType defs target alts
    = let res = filter (couldBe defs target) alts in
          if isNil res
             then alts -- if none of them work, better to show all the errors
             else res
