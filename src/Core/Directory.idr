module Core.Directory

import Core.Core

export
record Dirs where
  constructor MkDirs
  working_dir : String -- top level directory
  build_dir : String -- build directory, relative to working directory
  extra_dirs : List String -- places to look for source files

export
defaultDirs : Dirs
defaultDirs = MkDirs "." "build" []

-- findFile : String -> Dirs -> Core annot 
