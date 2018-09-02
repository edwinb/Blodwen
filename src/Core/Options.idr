module Core.Options

import Core.Core
import Core.Name
import Core.TTC
import Utils.Binary

public export
record LazyNames where
  constructor MkLazy
  active : Bool
  delayType : Name
  delay : Name
  force : Name

public export
record PairNames where
  constructor MkPairNs
  pairType : Name
  fstName : Name
  sndName : Name

public export
record PrimNames where
  constructor MkPrimNs
  fromIntegerName : Maybe Name
  fromStringName : Maybe Name
  fromCharName : Maybe Name

export
TTC annot LazyNames where
  toBuf b l
      = do toBuf b (delayType l)
           toBuf b (delay l)
           toBuf b (force l)
  fromBuf s b
      = do ty <- fromBuf s b
           d <- fromBuf s b
           f <- fromBuf s b
           pure (MkLazy True ty d f)

export
TTC annot PairNames where
  toBuf b l
      = do toBuf b (pairType l)
           toBuf b (fstName l)
           toBuf b (sndName l)
  fromBuf s b
      = do ty <- fromBuf s b
           d <- fromBuf s b
           f <- fromBuf s b
           pure (MkPairNs ty d f)

export
TTC annot PrimNames where
  toBuf b l
      = do toBuf b (fromIntegerName l)
           toBuf b (fromStringName l)
           toBuf b (fromCharName l)
  fromBuf s b
      = do i <- fromBuf s b
           str <- fromBuf s b
           c <- fromBuf s b
           pure (MkPrimNs i str c)

public export
record Dirs where
  constructor MkDirs
  build_dir : String -- build directory, relative to working directory
  dir_prefix : String -- installation prefix, for finding data files (e.g. run time support)
  extra_dirs : List String -- places to look for import files
  data_dirs : List String -- places to look for data file

public export
record PPrinter where
  constructor MkPPOpts
  showImplicits : Bool
  fullNamespace : Bool

public export
data CG = Chez 
        | Chicken
        | Racket

export
Eq CG where
  Chez == Chez = True
  Chicken == Chicken = True
  Racket == Racket = True
  _ == _ = False

export
TTC annot CG where
  toBuf b Chez = tag 0
  toBuf b Chicken = tag 1
  toBuf b Racket = tag 2

  fromBuf s b
      = case !getTag of
             0 => pure Chez
             1 => pure Chicken
             2 => pure Racket
             _ => corrupt "CG"

export
availableCGs : List (String, CG)
availableCGs = [("chez", Chez), ("chicken", Chicken), ("racket", Racket)]

export
getCG : String -> Maybe CG
getCG cg = lookup (toLower cg) availableCGs

-- Other options relevant to the current session (so not to be saved in a TTC)
public export
record Session where
  constructor MkSessionOpts
  quiet : Bool
  noprelude : Bool
  codegen : CG

-- NOTE: If adding options, remember to save any relevant ones in the TTC
-- implementation for Defs in Context.idr
public export
record Options where
  constructor MkOptions
  dirs : Dirs
  printing : PPrinter
  session : Session
  laziness : Maybe LazyNames
  pairnames : Maybe PairNames
  primnames : PrimNames

defaultDirs : Dirs
defaultDirs = MkDirs "build" "/usr/local" ["."] []

defaultPPrint : PPrinter
defaultPPrint = MkPPOpts False False

defaultSession : Session
defaultSession = MkSessionOpts False False Chez

export
defaults : Options
defaults = MkOptions defaultDirs defaultPPrint defaultSession 
                     Nothing Nothing (MkPrimNs Nothing Nothing Nothing)

-- Reset the options which are set by source files
export
clearNames : Options -> Options
clearNames = record { laziness = Nothing,
                      pairnames = Nothing,
                      primnames = MkPrimNs Nothing Nothing Nothing
                    } 

-- Some relevant options get stored in TTC; merge in the options from
-- a TTC file
export
mergeOptions : (ttcopts : Options) -> Options -> Options
mergeOptions ttcopts opts
  = record { laziness = laziness ttcopts <+> laziness opts,
             pairnames = pairnames ttcopts <+> pairnames opts,
             primnames = mergePrims (primnames ttcopts) (primnames opts)
           } opts
  where
    mergePrims : PrimNames -> PrimNames -> PrimNames
    mergePrims (MkPrimNs i s c) (MkPrimNs i' s' c')
        = MkPrimNs (i <+> i') (s <+> s') (c <+> c')

export
setLazy : (delayType : Name) -> (delay : Name) -> (force : Name) ->
          Options -> Options
setLazy ty d f = record { laziness = Just (MkLazy True ty d f) }

export
setPair : (pairType : Name) -> (fstn : Name) -> (sndn : Name) ->
          Options -> Options
setPair ty f s = record { pairnames = Just (MkPairNs ty f s) }

export
setFromInteger : Name -> Options -> Options
setFromInteger n = record { primnames->fromIntegerName = Just n }

export
setFromString : Name -> Options -> Options
setFromString n = record { primnames->fromStringName = Just n }

export
setFromChar : Name -> Options -> Options
setFromChar n = record { primnames->fromCharName = Just n }
