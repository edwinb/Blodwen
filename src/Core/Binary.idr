module Core.Binary

import Core.Context
import Core.Core
import Core.Options
import Core.TT
import Core.TTC
import Core.UnifyState

-- Reading and writing 'Defs' from/to  a binary file
-- In order to be saved, a name must have been flagged using 'toSave'.
-- (Otherwise we'd save out everything, not just the things in the current
-- file).

import public Utils.Binary

import Data.Buffer

%default covering

-- increment this when changing anything in the data format
-- NOTE: TTC files are only compatible if the version number is the same,
-- *and* the 'annot' type are the same, or there are no holes/constraints
ttcVersion : Int
ttcVersion = 1

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
  holes : List (annot, Name)
  constraints : Context (Constraint annot)
  context : Defs
  extraData : extra

-- NOTE: TTC files are only compatible if the version number is the same,
-- *and* the 'annot/extra' type are the same, or there are no holes/constraints
(TTC annot annot, TTC annot extra) => TTC annot (TTCFile annot extra) where
  toBuf b file
      = do toBuf b "TTC"
           toBuf b (version file)
           toBuf b (holes file)
           toBuf b (constraints file)
           toBuf b (context file)
           toBuf b (extraData file)

  fromBuf s b
      = do hdr <- fromBuf s b
           when (hdr /= "TTC") $ corrupt "header"
           ver <- fromBuf s b
           checkTTCVersion ver ttcVersion
           holes <- fromBuf s b
           constraints <- fromBuf s b
           defs <- fromBuf s b
           ex <- fromBuf s b
           pure (MkTTCFile ver holes constraints defs ex)

-- Update the various fields in Defs affected by the name's flags
processFlags : Name -> List DefFlag -> Defs -> Defs
processFlags n [] defs = defs
processFlags n (GlobalHint :: fs) defs
  = processFlags n fs (record { autoHints $= (n ::) } defs)
processFlags n (TypeHint ty :: fs) defs
  = processFlags n fs (addToTypeHints ty n defs)
processFlags n (Inline :: fs) defs = processFlags n fs defs

-- For every name (from 'toSave' in defs), add its definition and any
-- information from its flags to the new set of Defs that we'll write out
-- as Binary.
mkSaveDefs : List Name -> Defs -> Defs -> Defs
mkSaveDefs [] acc _ = acc
mkSaveDefs (n :: ns) acc defs
    = case lookupGlobalExact n (gamma defs) of
           Nothing => mkSaveDefs ns acc defs -- 'n' really should exist though!
           Just gdef =>
                let gam' = addCtxt n gdef (gamma acc) 
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
                         (record { options = options defs } initCtxt)
                         defs
         toBuf buf (MkTTCFile ttcVersion (holes ust) (constraints ust) defs'
                              extradata)
         Right ok <- coreLift $ writeToFile fname !(get Bin)
               | Left err => throw (InternalError (fname ++ ": " ++ show err))
         pure ()

-- Add definitions from a binary file to the current context
export
readFromTTC : (TTC annot annot, TTC annot extra) =>
              {auto c : Ref Ctxt Defs} ->
              {auto u : Ref UST (UState annot)} ->
              (fname : String) ->
              Core annot extra
readFromTTC fname
    = do Right buf <- coreLift $ readFromFile fname
               | Left err => throw (InternalError (fname ++ ": " ++ show err))
         bin <- newRef Bin buf -- for reading the file into
         sh <- initShare -- for recording string sharing
         tti <- fromBuf sh bin
         extend (context tti)
         ust <- get UST
         put UST (record { holes = holes tti,
                           constraints = constraints tti } ust)
         pure (extraData tti)
