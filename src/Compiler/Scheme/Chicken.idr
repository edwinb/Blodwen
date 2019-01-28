module Compiler.Scheme.Chicken

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.Scheme.Common

import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT

import Data.CMap
import Data.List
import Data.Vect
import System
import System.Info

import CompilerRuntime

%default covering

firstExists : List String -> BIO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

findCSI : BIO String
findCSI = pure "/usr/bin/env csi"

findCSC : BIO String
findCSC = pure "/usr/bin/env csc"

schHeader : List String -> String
schHeader ds
  = "(use numbers)\n" ++ unlines ds ++ "\n" ++
    "(let ()\n"

schFooter : String
schFooter = ")"

mutual
  chickenPrim : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  chickenPrim i vs CCall [ret, fn, args, world]
      = throw (InternalError ("Can't compile C FFI calls to Chicken Scheme yet"))
  chickenPrim i vs prim args 
      = schExtCommon chickenPrim i vs prim args

compileToSCM : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core annot ()
compileToSCM c tm outfile
    = do ds <- getDirectives Chicken
         (ns, tags) <- findUsedNames tm
         defs <- get Ctxt
         compdefs <- traverse (getScheme chickenPrim defs) ns
         let code = concat compdefs
         main <- schExp chickenPrim 0 [] !(compileExp tags tm)
         support <- readDataFile "chicken/support.scm"
         let scm = schHeader ds ++ support ++ code ++ main ++ schFooter
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()

compileExpr : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
compileExpr c tm outfile
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".scm"
         compileToSCM c tm outn
         csc <- coreLift findCSC
         ok <- coreLift $ system (csc ++ " " ++ outn ++ " -o " ++ outfile)
         if ok == 0
            then pure (Just outfile)
            else pure Nothing

executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core annot ()
executeExpr c tm
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".scm"
         compileToSCM c tm outn
         csi <- coreLift findCSI
         coreLift $ system (csi ++ " -s " ++ outn)
         pure ()

export
codegenChicken : Codegen annot
codegenChicken = MkCG compileExpr executeExpr

