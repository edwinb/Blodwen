module Core.Metadata

import Core.Binary
import Core.Context
import Core.Core
import Core.Normalise
import Core.TT
import Core.TTC

-- Additional data we keep about the context to support interactive editing

public export
record Metadata annot where
       constructor MkMetadata
       -- Mapping from source annotation (location, typically) to
       -- the LHS defined at that location. Also record the outer environment
       -- length, since we don't want to case split on these.
       lhsApps : List (annot, (Nat, ClosedTerm))
       -- Mapping from annotation the the name defined with that annotation,
       -- and its type (so, giving the ability to get the types of locally
       -- defined names)
       -- The type is abstracted over the whole environment; the Nat gives
       -- the number of names which were in the environment at the time
       names : List (annot, (Name, Nat, ClosedTerm))
       -- Mapping from annotation to the name that's declared there and
       -- its type; the Nat is as above
       tydecls : List (annot, (Name, Nat, ClosedTerm))
       -- Current lhs, if applicable, and a mapping from hole names to the
       -- lhs they're under. This is for expression search, to ensure that
       -- recursive calls have a smaller value as an argument.
       -- Also use this to get the name of the function being defined (i.e.
       -- to know what the recursive call is, if applicable)
       currentLHS : Maybe ClosedTerm
       holeLHS : List (Name, ClosedTerm)

export
initMetadata : Metadata annot
initMetadata = MkMetadata [] [] [] Nothing []

-- A label for metadata in the global state
export
data Meta : Type where

TTC annot annot => TTC annot (Metadata annot) where
  toBuf b m
      = do toBuf b (lhsApps m)
           toBuf b (names m)
           toBuf b (tydecls m)
           toBuf b (holeLHS m)

  fromBuf s b
      = do apps <- fromBuf s b
           ns <- fromBuf s b
           tys <- fromBuf s b
           hlhs <- fromBuf s b
           pure (MkMetadata apps ns tys Nothing hlhs)

export
addLHS : {auto m : Ref Meta (Metadata annot)} ->
         annot -> Nat -> Env Term vars -> Term vars -> Core annot ()
addLHS loc outerenvlen env tm
    = do meta <- get Meta
         put Meta (record { 
                      lhsApps $= ((loc, outerenvlen, bindEnv env tm) ::) 
                    } meta)

export
addNameType : {auto m : Ref Meta (Metadata annot)} ->
              annot -> Name -> Env Term vars -> Term vars -> Core annot ()
addNameType loc n env tm
    = do meta <- get Meta
         put Meta (record { 
                      names $= ((loc, (n, length env, bindEnv env tm)) ::) 
                    } meta)

export
addTyDecl : {auto m : Ref Meta (Metadata annot)} ->
            annot -> Name -> Env Term vars -> Term vars -> Core annot ()
addTyDecl loc n env tm
    = do meta <- get Meta
         put Meta (record { 
                      tydecls $= ((loc, (n, length env, bindEnv env tm)) ::) 
                    } meta)

export
setHoleLHS : {auto m : Ref Meta (Metadata annot)} ->
             ClosedTerm -> Core annot ()
setHoleLHS tm
    = do meta <- get Meta
         put Meta (record { currentLHS = Just tm } meta)

export
clearHoleLHS : {auto m : Ref Meta (Metadata annot)} ->
               Core annot ()
clearHoleLHS
    = do meta <- get Meta
         put Meta (record { currentLHS = Nothing } meta)

export
withCurrentLHS : {auto m : Ref Meta (Metadata annot)} ->
                 Name -> Core annot ()
withCurrentLHS n
    = do meta <- get Meta
         maybe (pure ())
               (\lhs => put Meta (record { holeLHS $= ((n, lhs) ::) } meta))
               (currentLHS meta)

findEntryWith : (annot -> a -> Bool) -> List (annot, a) -> Maybe (annot, a)
findEntryWith p [] = Nothing
findEntryWith p ((l, x) :: xs)
    = if p l x
         then Just (l, x)
         else findEntryWith p xs

export
findLHSAt : {auto m : Ref Meta (Metadata annot)} ->
            (annot -> ClosedTerm -> Bool) -> 
            Core annot (Maybe (annot, Nat, ClosedTerm))
findLHSAt p 
    = do meta <- get Meta
         pure (findEntryWith (\ loc, tm => p loc (snd tm)) (lhsApps meta))

export
findTypeAt : {auto m : Ref Meta (Metadata annot)} ->
             (annot -> (Name, Nat, ClosedTerm) -> Bool) -> 
             Core annot (Maybe (Name, Nat, ClosedTerm))
findTypeAt p
    = do meta <- get Meta
         pure (map snd (findEntryWith p (names meta)))

export
findTyDeclAt : {auto m : Ref Meta (Metadata annot)} ->
               (annot -> (Name, Nat, ClosedTerm) -> Bool) -> 
               Core annot (Maybe (annot, Name, Nat, ClosedTerm))
findTyDeclAt p
    = do meta <- get Meta
         pure (findEntryWith p (tydecls meta))

export
findHoleLHS : {auto m : Ref Meta (Metadata annot)} ->
              Name -> Core annot (Maybe ClosedTerm)
findHoleLHS hn
    = do meta <- get Meta
         pure (lookupBy (\x, y => dropNS x == dropNS y) hn (holeLHS meta))

-- Normalise all the types of the names, since they might have had holes
-- when added and the holes won't necessarily get saved
normaliseTypes : {auto m : Ref Meta (Metadata annot)} ->
                 {auto c : Ref Ctxt Defs} ->
                 Core annot ()
normaliseTypes
    = do meta <- get Meta
         defs <- get Ctxt
         put Meta (record { names $= map (nfType defs) } meta)
  where
    nfType : Defs -> (annot, (Name, Nat, ClosedTerm)) -> 
             (annot, (Name, Nat, ClosedTerm))
    nfType defs (loc, (n, len, ty)) = (loc, (n, len, normaliseHoles defs [] ty))

record TTMFile annot where
  constructor MkTTMFile
  version : Int
  metadata : Metadata annot

(TTC annot annot) => TTC annot (TTMFile annot) where
  toBuf b file
      = do toBuf b "TTM"
           toBuf b (version file)
           toBuf b (metadata file)

  fromBuf s b
      = do hdr <- fromBuf s b
           when (hdr /= "TTM") $ corrupt "TTM header"
           ver <- fromBuf s b
           checkTTCVersion ver ttcVersion
           md <- fromBuf s b
           pure (MkTTMFile ver md)

export
writeToTTM : (TTC annot annot) =>
             {auto c : Ref Ctxt Defs} ->
             {auto m : Ref Meta (Metadata annot)} ->
             (fname : String) ->
             Core annot ()
writeToTTM fname
    = do normaliseTypes
         buf <- initBinary
         meta <- get Meta
         toBuf buf (MkTTMFile ttcVersion meta)
         Right ok <- coreLift $ writeToFile fname !(get Bin)
             | Left err => throw (InternalError (fname ++ ": " ++ show err))
         pure ()

export
readFromTTM : (TTC annot annot) =>
              {auto m : Ref Meta (Metadata annot)} ->
              (fname : String) ->
              Core annot ()
readFromTTM fname
    = do Right buf <- coreLift $ readFromFile fname
             | Left err => throw (InternalError (fname ++ ": " ++ show err))
         bin <- newRef Bin buf
         sh <- initShare
         ttm <- fromBuf sh bin
         put Meta (metadata ttm)
