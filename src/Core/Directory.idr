module Core.Directory

import Core.Core

import System.Info

export
record Dirs where
  constructor MkDirs
  working_dir : String -- top level directory
  build_dir : String -- build directory, relative to working directory
  extra_dirs : List String -- places to look for source files

isWindows : Bool
isWindows = os `elem` ["win32", "mingw32", "cygwin32"]

sep : Char
sep = if isWindows then '\\' else '/'

fullPath : String -> List String
fullPath fp = filter (/="") $ split (==sep) fp

dropExtension : String -> String
dropExtension fname 
    = case span (/= '.') (reverse fname) of
           (all, "") => -- no extension
               reverse all
           (ext, root) => 
               -- assert that root can't be empty
               reverse (assert_total (strTail root))

export
defaultDirs : Dirs
defaultDirs = MkDirs "." "build" []

export
getTTCFileName : String -> String
getTTCFileName inp = dropExtension inp ++ ".ttc"

-- findFile : String -> Dirs -> Core annot 
