module Control.ST.FileIO

import Control.ST
import Control.IOExcept
import Core.Context

public export
interface FileIO (m : Type -> Type) where
  readFile : (fname : String) -> 
             STrans m (Either FileError String) xs (const xs)
  writeFile : (fname : String) -> (content : String) ->
              STrans m (Either FileError ()) xs (const xs)

export
FileIO IO where
  readFile f = lift (readFile f)
  writeFile f c = lift (writeFile f c)

export
FileIO (IOExcept Error) where
  readFile f = lift (ioe_lift (readFile f))
  writeFile f c = lift (ioe_lift (writeFile f c))
