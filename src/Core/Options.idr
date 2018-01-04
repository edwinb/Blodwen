module Core.Options

import Core.Directory

export
record Options where
  constructor MkOptions
  dirs : Dirs

export
defaults : Options
defaults = MkOptions defaultDirs
