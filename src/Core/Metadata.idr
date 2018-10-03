module Core.Metadata

import Core.Binary
import Core.Context
import Core.Core
import Core.TT
import Core.TTC

-- Additional data we keep about the context to support interactive editing

public export
record Metadata annot where
       constructor MkMetadata
       -- A mapping from source annotation (location, typically) to
       -- the LHS defined at that location
       lhsapps : List (annot, (vars ** Term vars))

export
initMetadata : Metadata annot
initMetadata = MkMetadata []

-- A label for metadata in the global state
export
data Meta : Type where

TTC annot annot => TTC annot (Metadata annot) where
  toBuf b m
      = do toBuf b (lhsapps m)

  fromBuf s b
      = do apps <- fromBuf s b
           pure (MkMetadata apps)

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
             {auto m : Ref Meta (Metadata annot)} ->
             (fname : String) ->
             Core annot ()
writeToTTM fname
    = do buf <- initBinary
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
