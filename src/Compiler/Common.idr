module Compiler.Common

import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.TT

import Data.CSet

%include C "sys/stat.h"

||| Generic interface to some code generator
||| @annot Type of error/annotations in Core
public export
record Codegen annot where
  constructor MkCG
  ||| Compile a Blodwen expression, saving it to a file.
  compileExpr : Ref Ctxt Defs ->
                ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
  ||| Execute a Blodwen expression directly.
  executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core annot ()

||| compile
||| Given a value of type Codegen, produce a standalone function
||| that executes the `compileExpr` method of the Codegen
export
compile : {auto c : Ref Ctxt Defs} ->
          Codegen annot ->
          ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
compile {c} cg = compileExpr cg c

||| execute
||| As with `compile`, produce a functon that executes
||| the `executeExpr` method of the given Codegen
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
         traverse inlineDef cns
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

