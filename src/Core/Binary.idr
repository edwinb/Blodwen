module Core.Binary

import Core.Context
import Core.Core
import Core.Hash
import Core.Normalise
import Core.Options
import Core.TT
import Core.TTC
import Core.UnifyState

-- Reading and writing 'Defs' from/to  a binary file
-- In order to be saved, a name must have been flagged using 'toSave'.
-- (Otherwise we'd save out everything, not just the things in the current
-- file).

import public Utils.Binary

import CompilerRuntime

%default covering

-- increment this when changing anything in the data format
-- NOTE: TTC files are only compatible if the version number is the same,
-- *and* the 'annot' type are the same, or there are no holes/constraints
export
ttcVersion : Int
ttcVersion = 29

export
checkTTCVersion : Int -> Int -> Core annot ()
checkTTCVersion ver exp
  = if ver < exp
       then throw (TTCError FormatOlder)
       else if ver > exp
            then throw (TTCError FormatNewer)
            else pure ()

record TTCFile annot extra where
  constructor MkTTCFile
  version : Int
  ifaceHash : Int
  importHashes : List (List String, Int)
  holes : List (annot, Name, Bool)
  constraints : Context (Constraint annot)
  context : Defs
  extraData : extra

-- NOTE: TTC files are only compatible if the version number is the same,
-- *and* the 'annot/extra' type are the same, or there are no holes/constraints
(TTC annot annot, TTC annot extra) => TTC annot (TTCFile annot extra) where
  toBuf b file
      = do toBuf b "TTC"
           toBuf b (version file)
           toBuf b (ifaceHash file)
           toBuf b (importHashes file)
           toBuf b (holes file)
           toBuf b (constraints file)
           toBuf b (context file)
           toBuf b (extraData file)

  fromBuf s b
      = do hdr <- fromBuf s b
           when (hdr /= "TTC") $ corrupt "TTC header"
           ver <- fromBuf s b
           checkTTCVersion ver ttcVersion
           ifaceHash <- fromBuf s b
           importHashes <- fromBuf s b
           holes <- fromBuf s b
           constraints <- fromBuf s b
           defs <- fromBuf s b
           ex <- fromBuf s b
           pure (MkTTCFile ver ifaceHash importHashes 
                           holes constraints defs ex)

-- Update the various fields in Defs affected by the name's flags
processFlags : Name -> List DefFlag -> Defs -> Defs
processFlags n [] defs = defs
processFlags n (GlobalHint t :: fs) defs
  = processFlags n fs (record { autoHints $= ((t, n) ::) } defs)
processFlags n (TypeHint ty d :: fs) defs
  = processFlags n fs (addToTypeHints ty n d defs)
processFlags n (Inline :: fs) defs = processFlags n fs defs
processFlags n (TCInline :: fs) defs = processFlags n fs defs
processFlags n (Invertible :: fs) defs = processFlags n fs defs
processFlags n (Overloadable :: fs) defs = processFlags n fs defs
processFlags n (SetTotal t :: fs) defs = processFlags n fs defs

-- For every name (from 'toSave' in defs), add its definition and any
-- information from its flags to the new set of Defs that we'll write out
-- as Binary.
mkSaveDefs : List Name -> Defs -> Defs -> Defs
mkSaveDefs [] acc _ = acc
mkSaveDefs (n :: ns) acc defs
    = case lookupGlobalExact n (gamma defs) of
           Nothing => mkSaveDefs ns acc defs -- 'n' really should exist though!
           Just gdef =>
                let gdef' = record { type $= normaliseHoles defs [] } gdef
                    gam' = addCtxt n gdef' (gamma acc) 
                    defs' = processFlags n (flags gdef) defs in
                    mkSaveDefs ns (record { gamma = gam' } acc) defs'

-- Write out the things in the context which have been defined in the
-- current source file
export
writeToTTC : (TTC annot annot, TTC annot extra) =>
             {auto c : Ref Ctxt Defs} ->
             {auto u : Ref UST (UState annot)} ->
             extra ->
             (fname : String) ->
             Core annot ()
writeToTTC extradata fname
    = do buf <- initBinary
         defs <- get Ctxt
         ust <- get UST
         let defs' = mkSaveDefs (getSave defs) 
                         (record { options = options defs,
                                   imported = imported defs,
                                   currentNS = currentNS defs,
                                   hiddenNames = hiddenNames defs,
                                   cgdirectives = cgdirectives defs
                                 } initCtxt)
                         defs
         log 5 $ "Writing " ++ fname ++ " with hash " ++ show (ifaceHash defs)
         toBuf buf (MkTTCFile ttcVersion (ifaceHash defs) (importHashes defs)
                              (holes ust) (constraints ust) defs'
                              extradata)
         Right ok <- coreLift $ writeToFile fname !(get Bin)
               | Left err => throw (InternalError (fname ++ ": " ++ show err))
         pure ()

-- Add definitions from a binary file to the current context
-- Returns the "extra" section of the file (user defined data), the interface
-- has and the list of additional TTCs that need importing
-- (we need to return these, rather than do it here, because after loading
-- the data that's when we process the extra data...)
export
readFromTTC : (TTC annot annot, TTC annot extra) =>
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              annot ->
              Bool ->
              (fname : String) -> -- file containing the module
              (modNS : List String) -> -- module namespace
              (importAs : List String) -> -- namespace to import as
              Core annot (Maybe (extra, Int, List (List String, Bool, List String)))
readFromTTC loc reexp fname modNS importAs
    = do defs <- get Ctxt
         -- If it's already in the context, don't load it again
         let False = (fname, importAs) `elem` allImported defs
              | True => pure Nothing
         put Ctxt (record { allImported $= ((fname, importAs) :: ) } defs)

         Right buf <- coreLift $ readFromFile fname
               | Left err => throw (InternalError (fname ++ ": " ++ show err))
         bin <- newRef Bin buf -- for reading the file into
         sh <- initShare -- for recording string sharing
         ttc <- fromBuf sh bin
         -- Rename everything in the ttc's context according to the namespace
         -- it was imported as
         -- [TODO]
         let renamed = context ttc

         -- Extend the current context with the updated definitions from the ttc
         extendAs loc reexp modNS importAs renamed
         setNS (currentNS (context ttc))

         -- Finally, update the unification state with the holes from the
         -- ttc
         ust <- get UST
         put UST (record { holes = holes ttc,
                           constraints = constraints ttc } ust)
         pure (Just (extraData ttc, ifaceHash ttc, imported (context ttc)))

getImportHashes : TTC annot annot =>
                  Ref Share (StringMap String) -> Ref Bin Binary ->
                  Core annot (List (List String, Int))
getImportHashes s b
    = do hdr <- fromBuf {a = String} s b
         when (hdr /= "TTC") $ corrupt "TTC header"
         ver <- fromBuf {a = Int} s b
         checkTTCVersion ver ttcVersion
         ifaceHash <- fromBuf {a = Int} s b
         fromBuf s b

getHash : TTC annot annot =>
          Ref Share (StringMap String) -> Ref Bin Binary ->
          Core annot Int
getHash s b
    = do hdr <- fromBuf {a = String} s b
         when (hdr /= "TTC") $ corrupt "TTC header"
         ver <- fromBuf {a = Int} s b
         checkTTCVersion ver ttcVersion
         fromBuf s b

export
readIFaceHash : TTC annot annot =>
                (fname : String) -> -- file containing the module
                Core annot Int
readIFaceHash fname
    = do Right buf <- coreLift $ readFromFile fname
            | Left err => pure 0
         b <- newRef Bin buf
         s <- initShare
         
         catch (getHash s b)
               (\err => pure 0)

export
readImportHashes : TTC annot annot =>
                (fname : String) -> -- file containing the module
                Core annot (List (List String, Int))
readImportHashes fname
    = do Right buf <- coreLift $ readFromFile fname
            | Left err => pure []
         b <- newRef Bin buf
         s <- initShare
         
         catch (getImportHashes s b)
               (\err => pure [])

         
