module Compiler.Scheme.Racket

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

findRacket : IO String
findRacket = pure "/usr/bin/env racket"

findRacoExe : IO String
findRacoExe = pure "raco exe"

schHeader : String
schHeader
  = "#lang racket/base\n" ++
    "(require racket/promise)\n" ++ -- for force/delay
    "(let ()\n"

schFooter : String
schFooter = ")"

mutual
  -- Need to convert the argument (a list of scheme arguments that may
  -- have been constructed at run time) to a scheme list to be passed to apply
  readArgs : SVars vars -> CExp vars -> Core annot String
  readArgs vs tm = pure $ "(blodwen-read-args " ++ !(schExp racketPrim vs tm) ++ ")"

  racketPrim : SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  racketPrim vs SchemeCall [ret, CPrimVal (Str fn), args, world]
     = pure $ mkWorld ("(apply " ++ fn ++" "
                  ++ !(readArgs vs args) ++ ")")
  racketPrim vs SchemeCall [ret, fn, args, world]
     = pure $ mkWorld ("(apply (eval (string->symbol " ++ !(schExp racketPrim vs fn) ++")) "
                  ++ !(readArgs vs args) ++ ")")
  racketPrim vs CCall [ret, fn, args, world]
      = throw (InternalError ("Can't compile C FFI calls to Racket yet"))
  racketPrim vs PutStr [arg, world] 
      = pure $ "(display " ++ !(schExp racketPrim vs arg) ++ ") " ++ mkWorld (schConstructor 0 []) -- code for MkUnit
  racketPrim vs GetStr [world] 
      = pure $ mkWorld "(read-line (current-input-port))"
  racketPrim vs (Unknown n) args 
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  racketPrim vs prim args 
      = throw (InternalError ("Badly formed external primitive " ++ show prim))

compileToRKT : Ref Ctxt Defs ->
               ClosedTerm -> (outfile : String) -> Core annot ()
compileToRKT c tm outfile
    = do ns <- findUsedNames tm
         defs <- get Ctxt
         compdefs <- traverse (getScheme racketPrim defs) ns
         let code = concat compdefs
         main <- schExp racketPrim [] !(compileExp tm)
         support <- readDataFile "racket/support.rkt"
         let scm = schHeader ++ support ++ code ++ "(void " ++ main ++ ")\n" ++ schFooter
         Right () <- coreLift $ writeFile outfile scm
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()

compileExpr : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core annot ()
compileExpr c tm outfile
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".rkt"
         compileToRKT c tm outn
         raco <- coreLift findRacoExe
         ok <- coreLift $ system (raco ++ " -o " ++ outfile ++ " " ++ outn)
         if ok == 0
            then putStrLnQ $ outfile ++ " written"
            else pure ()

executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core annot ()
executeExpr c tm
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".rkt"
         compileToRKT c tm outn
         racket <- coreLift findRacket
         coreLift $ system (racket ++ " " ++ outn)
         pure ()

export
codegenRacket : Codegen annot
codegenRacket = MkCG compileExpr executeExpr

