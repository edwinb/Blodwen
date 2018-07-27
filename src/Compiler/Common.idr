module Compiler.Common

import Compiler.CompileExpr

import Core.Context
import Core.TT

import Data.CSet

%include C "sys/stat.h"
    
getAllDesc : List Name -> SortedSet -> Gamma -> SortedSet
getAllDesc [] ns g = ns
getAllDesc (n :: rest) ns g
  = if contains n ns
       then getAllDesc rest ns g
       else case lookupGlobalExact n g of
                 Nothing => getAllDesc rest ns g
                 Just def => -- assert_total $
                   let refs = refersTo def in
                       getAllDesc (rest ++ refs) (insert n ns) g

-- This is a duplicate of the function in Core.Context, but here we need to guarantee
-- we get *all* descendents, not just ones we may need for the occurs check.
-- TODO: Tidy this up.
getDesc : Name -> Gamma -> List Name
getDesc n g
    = CSet.toList $ getAllDesc [n] empty g

-- Find all the names which need compiling, from a given expression, and compile
-- them to CExp form (and update that in the Defs)
export
findUsedNames : {auto c : Ref Ctxt Defs} -> Term vars -> Core annot (List Name)
findUsedNames tm
    = do defs <- get Ctxt
         let ns = toList (getRefs tm)
         let allNs = ns ++ concatMap (\n => getDesc n (gamma defs)) ns
         let cns = toList (fromList allNs)
         traverse compileDef cns
         pure cns

-- Some things missing from Prelude.File

export
exists : String -> IO Bool
exists f 
    = do Right ok <- openFile f Read
             | Left err => pure False
         closeFile ok
         pure True

export
tmpName : IO String
tmpName = foreign FFI_C "tmpnam" (Ptr -> IO String) null

export
chmod : String -> Int -> IO ()
chmod f m = foreign FFI_C "chmod" (String -> Int -> IO ()) f m

