module Interfaces.FileIO

import Control.Monad.StateE
import Control.IOExcept
import Core.Context

public export
interface FileIO (m : Type -> Type) where
  readFile : (fname : String) -> 
             SE s err m (Either FileError String)
  writeFile : (fname : String) -> (content : String) ->
              SE s err m (Either FileError ())

export
FileIO IO where
  readFile f = lift (readFile f)
  writeFile f c = lift (writeFile f c)

export
FileIO (IOExcept (Error annot)) where
  readFile f = lift (ioe_lift (readFile f))
  writeFile f c = lift (ioe_lift (writeFile f c))
