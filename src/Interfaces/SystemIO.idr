module Interfaces.SystemIO

import Control.Monad.StateE
import Core.Context

import CompilerRuntime

public export
interface SystemIO (m : Type -> Type) where
  getArgs : SE s err m (List String)

export
SystemIO IO where
  getArgs = lift getArgs

export
SystemIO BIO where
  getArgs = lift getArgs

export
SystemIO (BIOExcept (Error annot)) where
  getArgs = lift (ioe_lift getArgs)
