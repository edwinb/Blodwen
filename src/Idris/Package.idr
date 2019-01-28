module Idris.Package

import Core.Context
import Core.Core
import Core.Directory
import Core.Options
import Core.Unify

import Control.Catchable

import Idris.CommandLine
import Idris.ModTree
import Idris.ProcessIdr
import Idris.REPLOpts
import Idris.SetOptions
import Idris.Syntax
import Parser.Lexer
import Parser.Support
import Utils.Binary

-- import System
import Text.Parser

import CompilerRuntime

%default covering

record PkgDesc where
  constructor MkPkgDesc
  name : String
  version : String
  authors : String
  depends : List String -- packages to add to search path
  modules : List (List String, String) -- modules to install (namespace, filename)
  mainmod : Maybe (List String, String) -- main file (i.e. file to load at REPL)
  executable : Maybe String -- name of executable
  options : Maybe (FC, String)
  prebuild : Maybe (FC, String) -- Script to run before building
  postbuild : Maybe (FC, String) -- Script to run after building
  preinstall : Maybe (FC, String) -- Script to run after building, before installing
  postinstall : Maybe (FC, String) -- Script to run after installing

Show PkgDesc where
  show pkg = "Package: " ++ name pkg ++ "\n" ++
             "Version: " ++ version pkg ++ "\n" ++
             "Authors: " ++ authors pkg ++ "\n" ++
             "Depends: " ++ show (depends pkg) ++ "\n" ++
             "Modules: " ++ show (map snd (modules pkg)) ++ "\n" ++
             maybe "" (\m => "Main: " ++ snd m ++ "\n") (mainmod pkg) ++
             maybe "" (\m => "Exec: " ++ m ++ "\n") (executable pkg) ++
             maybe "" (\m => "Opts: " ++ snd m ++ "\n") (options pkg) ++
             maybe "" (\m => "Prebuild: " ++ snd m ++ "\n") (prebuild pkg) ++
             maybe "" (\m => "Postbuild: " ++ snd m ++ "\n") (postbuild pkg) ++
             maybe "" (\m => "Preinstall: " ++ snd m ++ "\n") (preinstall pkg) ++
             maybe "" (\m => "Postinstall: " ++ snd m ++ "\n") (postinstall pkg)

initPkgDesc : String -> PkgDesc
initPkgDesc pname
    = MkPkgDesc pname "0" "Anonymous" [] []
                Nothing Nothing Nothing Nothing Nothing Nothing Nothing

data DescField : Type where
  PVersion : FC -> String -> DescField
  PAuthors : FC -> String -> DescField
  PDepends : List String -> DescField
  PModules : List (FC, List String) -> DescField
  PMainMod : FC -> List String -> DescField
  PExec : String -> DescField
  POpts : FC -> String -> DescField
  PPrebuild : FC -> String -> DescField
  PPostbuild : FC -> String -> DescField
  PPreinstall : FC -> String -> DescField
  PPostinstall : FC -> String -> DescField

field : String -> Rule DescField
field fname
      = strField PVersion "version"
    <|> strField PAuthors "authors"
    <|> strField POpts "options"
    <|> strField POpts "opts"
    <|> strField PPrebuild "prebuild"
    <|> strField PPostbuild "postbuild"
    <|> strField PPreinstall "preinstall"
    <|> strField PPostinstall "postinstall"
    <|> do exactIdent "depends"; symbol "="
           ds <- sepBy1 (symbol ",") unqualifiedName
           pure (PDepends ds)
    <|> do exactIdent "modules"; symbol "="
           ms <- sepBy1 (symbol ",") 
                      (do start <- location
                          ns <- namespace_
                          end <- location
                          pure (MkFC fname start end, ns))
           pure (PModules ms)
    <|> do exactIdent "main"; symbol "="
           start <- location
           m <- namespace_
           end <- location
           pure (PMainMod (MkFC fname start end) m)
    <|> do exactIdent "executable"; symbol "="
           e <- unqualifiedName
           pure (PExec e)
  where
    getStr : (FC -> String -> DescField) -> FC ->
             String -> Constant -> EmptyRule DescField
    getStr p fc fld (Str s) = pure (p fc s)
    getStr p fc fld _ = fail $ fld ++ " field must be a string"

    strField : (FC -> String -> DescField) -> String -> Rule DescField
    strField p f
        = do start <- location
             exactIdent f
             symbol "="
             c <- constant
             end <- location
             getStr p (MkFC fname start end) f c

parsePkgDesc : String -> Rule (String, List DescField)
parsePkgDesc fname
    = do exactIdent "package"
         name <- unqualifiedName
         fields <- many (field fname)
         pure (name, fields)

addField : {auto c : Ref Ctxt Defs} ->
           DescField -> PkgDesc -> Core FC PkgDesc
addField (PVersion fc n) pkg = pure (record { version = n } pkg)
addField (PAuthors fc a) pkg = pure (record { authors = a } pkg)
addField (PDepends ds) pkg = pure (record { depends = ds } pkg)
addField (PModules ms) pkg 
    = pure (record { modules = !(traverse toSource ms) } pkg)
  where
    toSource : (FC, List String) -> Core FC (List String, String)
    toSource (loc, ns) = pure (ns, !(nsToSource loc ns))
addField (PMainMod loc n) pkg
    = pure (record { mainmod = Just (n, !(nsToSource loc n)) } pkg)
addField (PExec e) pkg = pure (record { executable = Just e } pkg)
addField (POpts fc e) pkg = pure (record { options = Just (fc, e) } pkg)
addField (PPrebuild fc e) pkg = pure (record { prebuild = Just (fc, e) } pkg)
addField (PPostbuild fc e) pkg = pure (record { postbuild = Just (fc, e) } pkg)
addField (PPreinstall fc e) pkg = pure (record { preinstall = Just (fc, e) } pkg)
addField (PPostinstall fc e) pkg = pure (record { postinstall = Just (fc, e) } pkg)

addFields : {auto c : Ref Ctxt Defs} ->
            List DescField -> PkgDesc -> Core FC PkgDesc
addFields [] desc = pure desc
addFields (x :: xs) desc = addFields xs !(addField x desc)

runScript : Maybe (FC, String) -> Core FC ()
runScript Nothing = pure ()
runScript (Just (fc, s)) 
    = do res <- coreLift $ system s
         when (res /= 0) $
            throw (GenericMsg fc "Script failed")

addDeps : {auto c : Ref Ctxt Defs} ->
          PkgDesc -> Core FC ()
addDeps pkg
    = do defs <- get Ctxt
         traverse addPkgDir (depends pkg)
         pure ()

processOptions : {auto c : Ref Ctxt Defs} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 Maybe (FC, String) -> Core FC ()
processOptions Nothing = pure ()
processOptions (Just (fc, opts))
    = do let Right clopts = getOpts (words opts)
                | Left err => throw (GenericMsg fc err)
         preOptions clopts 

build : {auto c : Ref Ctxt Defs} ->
        {auto s : Ref Syn SyntaxInfo} ->
        {auto o : Ref ROpts REPLOpts} ->
        PkgDesc -> Core FC (List (Error FC))
build pkg
    = do defs <- get Ctxt
         addDeps pkg
         processOptions (options pkg)
         runScript (prebuild pkg)
         let toBuild = maybe (map snd (modules pkg))
                             (\m => snd m :: map snd (modules pkg))
                             (mainmod pkg)
         [] <- buildAll toBuild
              | errs => pure errs
         runScript (postbuild pkg)
         pure []

copyFile : String -> String -> BIO (Either FileError ())
copyFile src dest
    = do Right buf <- readFromFile src
             | Left err => pure (Left err)
         writeToFile dest buf

installFrom : {auto c : Ref Ctxt Defs} ->
              String -> String -> String -> List String -> Core FC ()
installFrom _ _ _ [] = pure ()
installFrom pname builddir destdir ns@(m :: dns)
    = do defs <- get Ctxt
         let modname = showSep "." (reverse ns)
         let ttcfile = showSep "/" (reverse ns)
         let ttcPath = builddir ++ dirSep ++ ttcfile ++ ".ttc"
         let destPath = destdir ++ dirSep ++ showSep "/" (reverse dns)
         let destFile = destdir ++ dirSep ++ ttcfile ++ ".ttc"
         Right _ <- coreLift $ mkdirs (reverse dns) 
             | Left err => throw (FileErr pname err)
         coreLift $ putStrLn $ "Installing " ++ ttcPath ++ " to " ++ destPath
         Right _ <- coreLift $ copyFile ttcPath destFile
             | Left err => throw (FileErr pname err)
         pure ()

-- Install all the built modules in prefix/package/
-- We've already built and checked for success, so if any don't exist that's
-- an internal error.
install : {auto c : Ref Ctxt Defs} -> 
          {auto o : Ref ROpts REPLOpts} ->
          PkgDesc -> Core FC ()
install pkg 
    = do defs <- get Ctxt
         let build = build_dir (dirs (options defs))
         runScript (preinstall pkg)
         let toInstall = maybe (map fst (modules pkg))
                               (\m => fst m :: map fst (modules pkg))
                               (mainmod pkg)
         srcdir <- coreLift currentDir
         -- Make the package installation directory
         let installPrefix = dir_prefix (dirs (options defs)) ++ dirSep ++ "blodwen"
         True <- coreLift $ changeDir installPrefix
             | False => throw (FileErr (name pkg) FileReadError)
         Right _ <- coreLift $ mkdirs [name pkg]
             | Left err => throw (FileErr (name pkg) err)
         True <- coreLift $ changeDir (name pkg)
             | False => throw (FileErr (name pkg) FileReadError)

         -- We're in that directory now, so copy the files from 
         -- srcdir/build into it
         traverse (installFrom (name pkg)
                               (srcdir ++ dirSep ++ build) 
                               (installPrefix ++ dirSep ++ name pkg)) toInstall
         coreLift $ changeDir srcdir
         runScript (postinstall pkg)

-- Just load the 'Main' module, if it exists, which will involve building
-- it if necessary
runRepl : {auto c : Ref Ctxt Defs} -> 
          {auto o : Ref ROpts REPLOpts} ->
          PkgDesc -> Core FC ()
runRepl pkg 
    = do addDeps pkg 
         processOptions (options pkg)
         throw (InternalError "Not implemented")

processPackage : {auto c : Ref Ctxt Defs} ->
                 {auto s : Ref Syn SyntaxInfo} ->
                 {auto o : Ref ROpts REPLOpts} ->
                 PkgCommand -> String -> Core FC ()
processPackage cmd file 
    = do Right (pname, fs) <- coreLift $ parseFile file 
                                  (do desc <- parsePkgDesc file
                                      eoi
                                      pure desc)
             | Left err => throw (ParseFail (getParseErrorLoc file err) err)
         pkg <- addFields fs (initPkgDesc pname)
         case cmd of
              Build => do [] <- build pkg
                             | errs => coreLift (exit 1)
                          pure ()
              Install => do [] <- build pkg
                               | errs => coreLift (exit 1)
                            install pkg
              REPL => runRepl pkg

rejectPackageOpts : List CLOpt -> Core FC Bool
rejectPackageOpts (Package cmd f :: _)
    = do coreLift $ putStrLn ("Package commands (--build, --install --repl) must be the only option given")
         pure True -- Done, quit here
rejectPackageOpts (_ :: xs) = rejectPackageOpts xs
rejectPackageOpts [] = pure False

-- If there's a package option, it must be the only option, so reject if
-- it's not
export
processPackageOpts : {auto c : Ref Ctxt Defs} ->
                     {auto s : Ref Syn SyntaxInfo} ->
                     {auto o : Ref ROpts REPLOpts} ->
                     List CLOpt -> Core FC Bool
processPackageOpts [Package cmd f] 
    = do processPackage cmd f
         pure True
processPackageOpts opts = rejectPackageOpts opts
