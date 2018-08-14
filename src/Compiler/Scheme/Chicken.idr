module Compiler.Scheme.Chicken

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.Scheme.Common

import Core.Context
import Core.Directory
import Core.Name
import Core.TT

import Data.List
import Data.Vect
import System
import System.Info

%default covering

firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

findCSI : IO String
findCSI = pure "/usr/bin/env csi"

findCSC : IO String
findCSC = pure "/usr/bin/env csc"

schHeader : String
schHeader
  = "(use numbers)\n\n" ++
    "(let ()\n"

schFooter : String
schFooter = ")"

mutual
  -- Need to convert the argument (a list of scheme arguments that may
  -- have been constructed at run time) to a scheme list to be passed to apply
  readArgs : SVars vars -> CExp vars -> Core annot String
  readArgs vs tm = pure $ "(blodwen-read-args " ++ !(schExp chickenPrim vs tm) ++ ")"

  chickenPrim : SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  chickenPrim vs SchemeCall [ret, CPrimVal (Str fn), args, world]
     = pure $ mkWorld ("(apply " ++ fn ++" "
                  ++ !(readArgs vs args) ++ ")")
  chickenPrim vs SchemeCall [ret, fn, args, world]
     = pure $ mkWorld ("(apply (eval (string->symbol " ++ !(schExp chickenPrim vs fn) ++")) "
                  ++ !(readArgs vs args) ++ ")")
  chickenPrim vs CCall [ret, fn, args, world]
      = throw (InternalError ("Can't compile C FFI calls to Chicken Scheme yet"))
  chickenPrim vs PutStr [arg, world] 
      = pure $ "(display " ++ !(schExp chickenPrim vs arg) ++ ") " ++ mkWorld (schConstructor 0 []) -- code for MkUnit
  chickenPrim vs GetStr [world] 
      = pure $ mkWorld "(read-line (current-input-port))"
  chickenPrim vs (Unknown n) args 
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  chickenPrim vs prim args 
      = throw (InternalError ("Badly formed external primitive " ++ show prim))

compileToSCM : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core annot ()
compileToSCM c tm outfile
    = do ns <- findUsedNames tm
         defs <- get Ctxt
         compdefs <- traverse (getScheme chickenPrim defs) ns
         let code = concat compdefs
         main <- schExp chickenPrim [] !(compileExp tm)
         support <- readDataFile "chicken/support.scm"
         let scm = schHeader ++ support ++ code ++ main ++ schFooter
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()

compileExpr : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core annot ()
compileExpr c tm outfile
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".scm"
         compileToSCM c tm outn
         csc <- coreLift findCSC
         ok <- coreLift $ system (csc ++ " " ++ outn ++ " -o " ++ outfile)
         if ok == 0
            then putStrLnQ $ outfile ++ " written"
            else pure ()

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

