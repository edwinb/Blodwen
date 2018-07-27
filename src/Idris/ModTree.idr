module Idris.ModTree

import Core.Binary
import Core.Context
import Core.Core
import Core.Directory
import Core.Options
import Core.Primitives
import Core.InitPrimitives
import Core.UnifyState

import Idris.Desugar
import Idris.Parser
import Idris.ProcessIdr
import Idris.Syntax

%default covering

record ModTree where
  constructor MkModTree
  nspace : List String
  sourceFile : Maybe String
  deps : List ModTree

-- A module file to build, and its list of dependencies
-- From this we can work out if the source file needs rebuilding, assuming
-- things are build in dependency order. A source file needs rebuilding
-- if:
--  + Its corresponding ttc is older than the source file
--  + Any of the import ttcs are *newer* than the corresponding ttc
--    (If so: also any imported ttc's fingerprint is different from the one
--    stored in the source file's ttc) 
public export
record BuildMod where
  constructor MkBuildMod
  buildFile : Maybe String
  buildNS : List String
  imports : List (List String)

export
Show BuildMod where
  show t = case buildFile t of
                Nothing => ""
                Just fname => fname ++ " [" ++ 
                                  showSep ", " (map showNS (imports t))
                                     ++ "]"
    where
      showNS : List String -> String
      showNS ns = showSep "." (reverse ns)

readHeader : {auto c : Ref Ctxt Defs} ->
             annot -> (mod : List String) -> Core annot (String, Module)
readHeader loc mod
    = do path <- nsToSource loc mod
         Right res <- coreLift (readFile path)
            | Left err => throw (FileErr path err)
         case runParser res (progHdr path) of
              Left err => throw (ParseFail err)
              Right mod => pure (path, mod)

data AllMods : Type where

mkModTree : {auto c : Ref Ctxt Defs} ->
            {auto a : Ref AllMods (List (List String, ModTree))} ->
            annot -> 
            (done : List (List String)) -> -- if 'mod' is here we have a cycle
            (mod : List String) ->
            Core annot ModTree
mkModTree loc done mod
  = if mod `elem` done
       then throw (CyclicImports (done ++ [mod]))
       else 
          -- Read imports from source file. If the source file isn't
          -- available, it's not our responsibility
          catch (do all <- get AllMods
                    -- If we've seen it before, reuse what we found
                    case lookup mod all of
                         Nothing =>
                           do (file, modInfo) <- readHeader loc mod
                              let imps = map path (imports modInfo)
                              ms <- traverse (mkModTree loc done) imps
                              let mt = MkModTree mod (Just file) ms
                              all <- get AllMods
                              put AllMods ((mod, mt) :: all)
                              pure mt
                         Just m => pure m)
                -- Couldn't find source, assume it's in a package directory
                (\err => pure (MkModTree mod Nothing []))

-- Given a module tree, returns the modules in the reverse order they need to
-- be built, including their dependencies
mkBuildMods : List BuildMod -> ModTree -> List BuildMod
mkBuildMods acc mod
    = let req = buildDeps acc (reverse (deps mod)) in
          if sourceFile mod `elem` map buildFile req
             then req
             else MkBuildMod (sourceFile mod) (nspace mod) 
                             (map nspace (deps mod)) :: req
  where
    buildDeps : List BuildMod -> List ModTree -> List BuildMod
    buildDeps acc [] = acc
    buildDeps acc (m :: ms) = buildDeps (mkBuildMods acc m) ms

-- Given a main file name, return the list of modules that need to be
-- built for that main file, in the order they need to be built
export
getBuildMods : {auto c : Ref Ctxt Defs} ->
               annot -> (mainFile : String) -> Core annot (List BuildMod)
getBuildMods loc fname
    = do a <- newRef AllMods []
         t <- mkModTree {a} loc [] (pathToNS fname)
         pure (reverse (mkBuildMods [] t))

fnameModified : String -> Core annot Integer
fnameModified fname
    = do Right f <- coreLift $ openFile fname Read
             | Left err => throw (FileErr fname err)
         Right t <- coreLift $ fileModifiedTime f
             | Left err => throw (FileErr fname err)
         coreLift $ closeFile f
         pure t

-- Print, but only when not in quiet mode
export
putStrQ : {auto c : Ref Ctxt Defs} ->
          String -> Core annot ()
putStrQ str
    = when (not (quiet !getSession)) $
         coreLift $ putStr str

export
putStrLnQ : {auto c : Ref Ctxt Defs} ->
            String -> Core annot ()
putStrLnQ str = putStrQ (str ++ "\n")

buildMod : {auto c : Ref Ctxt Defs} ->
           FC -> Nat -> Nat -> BuildMod -> Core FC Bool
-- Build from source if any of the dependencies, or the associated source
-- file, have a modification time which is newer than the module's ttc
-- file
buildMod loc num len mod
   = do clearCtxt; addPrimitives
        let Just src = buildFile mod
            | Nothing => pure True -- No source file, nothing to build
        mttc <- getTTCFileName src
        depFiles <- traverse (nsToPath loc) (imports mod)
        ttcTime <- catch (do t <- fnameModified mttc
                             pure (Just t))
                         (\err => pure Nothing)
        srcTime <- fnameModified src
        depTimes <- traverse (\f => do t <- fnameModified f
                                       pure (f, t)) depFiles
        let needsBuilding =
               case ttcTime of
                    Nothing => True
                    Just t => any (\x => x > t) (srcTime :: map snd depTimes)
        u <- newRef UST initUState
        s <- newRef Syn initSyntax

        let showMod = showSep "." (reverse (buildNS mod))

        if needsBuilding
           then do putStrLnQ $ show num ++ "/" ++ show len ++
                                   ": Building " ++ showMod ++
                                   " (" ++ src ++ ")"
                   process {u} {s} src
           else pure True

buildMods : {auto c : Ref Ctxt Defs} ->
            FC -> Nat -> Nat -> List BuildMod -> Core FC Bool
buildMods fc num len [] = pure True
buildMods fc num len (m :: ms)
    = do ok <- buildMod fc num len m
         if ok
            then buildMods fc (1 + num) len ms
            else pure False

export
buildAll : {auto c : Ref Ctxt Defs} ->
           {auto u : Ref UST (UState FC)} ->
           {auto s : Ref Syn SyntaxInfo} ->
           (mainFile : String) -> Core FC ()
buildAll fname
    = do mods <- getBuildMods toplevelFC fname
         ok <- buildMods toplevelFC 1 (length mods) mods
         if ok
            then do -- On success, reload the main ttc in a clean context
                    clearCtxt; addPrimitives
                    mainttc <- getTTCFileName fname
                    readAsMain mainttc
            else pure () -- Error happened, give up

