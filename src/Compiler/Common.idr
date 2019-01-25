module Compiler.Common

import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.TT

import Data.CMap
import Data.CSet

%include C "sys/stat.h"
    
public export
record Codegen annot where
  constructor MkCG
  compileExpr : Ref Ctxt Defs -> 
                ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
  executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core annot ()

export
compile : {auto c : Ref Ctxt Defs} ->
          Codegen annot ->
          ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
compile {c} cg = compileExpr cg c

export
execute : {auto c : Ref Ctxt Defs} ->
          Codegen annot ->
          ClosedTerm -> Core annot ()
execute {c} cg = executeExpr cg c

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

-- Calculate a unique tag for each type constructor name we're compiling
-- This is so that type constructor names get globally unique tags
mkNameTags : Defs -> NameTags -> Int -> List Name -> NameTags
mkNameTags defs tags t [] = tags
mkNameTags defs tags t (n :: ns)
    = case lookupDefExact n (gamma defs) of
           Just (TCon _ _ _ _ _ _)
              => mkNameTags defs (insert n t tags) (t + 1) ns
           _ => mkNameTags defs tags t ns

-- Find all the names which need compiling, from a given expression, and compile
-- them to CExp form (and update that in the Defs)
export
findUsedNames : {auto c : Ref Ctxt Defs} -> Term vars -> Core annot (List Name, NameTags)
findUsedNames tm
    = do defs <- get Ctxt
         let ns = toList (getRefs tm)
         let allNs = ns ++ concatMap (\n => getDesc n (gamma defs)) ns
         let cns = toList (fromList allNs)
         -- Initialise the type constructor list with explicit names for
         -- the primitives (this is how we look up the tags)
         let tyconInit = insert (UN "Type") 7 
                           (primTags 1 empty 
                                     [IntType, IntegerType, StringType,
                                      CharType, DoubleType, WorldType])
         let tycontags = mkNameTags defs tyconInit 100 cns
         traverse (compileDef tycontags) cns
         traverse inlineDef cns
         pure (cns, tycontags)
  where
    primTags : Int -> NameTags -> List Constant -> NameTags
    primTags t tags [] = tags
    primTags t tags (c :: cs)
        = primTags (t + 1) (insert (UN (show c)) t tags) cs

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

