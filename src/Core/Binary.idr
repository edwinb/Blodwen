module Core.Binary

import Core.Context
import Core.Core
import Core.TT

import public Utils.Binary

import Data.Buffer

%default covering

-- increment this when changing anything in the data format
ttiVersion : Int
ttiVersion = 0

checkTTIVersion : Int -> Int -> Core annot ()
checkTTIVersion ver exp
  = if ver < exp
       then throw (TTIError FormatOlder)
       else if ver > exp
            then throw (TTIError FormatNewer)
            else pure ()

record TTIFile where
  constructor MkTTIFile
  version : Int
  -- TODO: Also need 'constraints' from UnifyState in case any are exported
  -- due to having named holes with constraints.
  context : Defs

TTI TTIFile where
  toBuf b file
      = do toBuf b "TTI"
           toBuf b (version file)
           toBuf b (context file)

  fromBuf b
      = do hdr <- fromBuf b {a = String}
           when (hdr /= "TTI") $ corrupt "header"
           ver <- fromBuf b {a = Int}
           checkTTIVersion ver ttiVersion
           defs <- fromBuf b {a = Defs}
           pure (MkTTIFile ver defs)

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
writeToTTI : {auto c : Ref Ctxt Defs} ->
             (fname : String) ->
             Core annot ()
writeToTTI fname
    = do buf <- initBinary
         defs <- get Ctxt
         let defs' = mkSaveDefs (getSave defs) initCtxt defs
         toBuf buf (MkTTIFile ttiVersion defs')
         Right ok <- coreLift $ writeToFile fname !(get Bin)
               | Left err => throw (InternalError (fname ++ ": " ++ show err))
         pure ()

-- Add definitions from a binary file to the current context
export
readFromTTI : {auto c : Ref Ctxt Defs} ->
              (fname : String) ->
              Core annot ()
readFromTTI fname
    = do Right buf <- coreLift $ readFromFile fname
               | Left err => throw (InternalError (fname ++ ": " ++ show err))
         bin <- newRef Bin buf
         defs <- fromBuf bin
         extend defs
         
