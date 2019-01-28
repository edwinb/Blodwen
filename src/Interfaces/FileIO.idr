module Interfaces.FileIO

import Control.Monad.StateE
import Core.Context
import CompilerRuntime

public export
interface FileIO (m : Type -> Type) where
  readFile : (fname : String) -> 
             SE s err m (Either FileError String)
  writeFile : (fname : String) -> (content : String) ->
              SE s err m (Either FileError ())

export
FileIO BIO where
  readFile f = lift (readFile f)
  writeFile f c = lift (writeFile f c)

export
FileIO (BIOExcept (Error annot)) where
  -- not handling errors for now
  readFile f = lift (ioe_lift (readFile f))
  writeFile f c = lift (ioe_lift (writeFile f c))
