module Control.ST.SystemIO

import Control.ST
import Control.IOExcept
import Core.Context

public export
interface SystemIO (m : Type -> Type) where
  getArgs : STrans m (List String) xs (const xs)

export
SystemIO IO where
  getArgs = lift getArgs

export
SystemIO (IOExcept Error) where
  getArgs = lift (ioe_lift getArgs)
