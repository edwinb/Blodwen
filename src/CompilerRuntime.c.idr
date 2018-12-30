module CompilerRuntime

import public Control.IOExcept
import public IO
import public Prelude.File
import public System
import public Data.Buffer
import public Data.IORef

public export
BIO : Type -> Type
BIO = IO

public export
BIORef : Type -> Type
BIORef = IORef

public export
bChangeDir : String -> BIO Bool
bChangeDir = Prelude.File.changeDir

public export
bPrintLn : Show ty => ty -> BIO ()
bPrintLn = Prelude.Interactive.printLn

public export
bPutChar : Char -> BIO () 
bPutChar = Prelude.Interactive.putChar

public export
bGetChar : BIO Char
bGetChar = Prelude.Interactive.getChar

public export
BIOExcept : Type -> Type -> Type
BIOExcept = IOExcept' FFI_C

public export
BFile : Type
BFile = Prelude.File.File

public export
BFileError : Type
BFileError = Prelude.File.FileError

public export
cannotOpenFile : String -> BFileError
cannotOpenFile fn = GenericFileError 0

public export
bOpenFile : (f : String) -> (m : Mode) -> BIO (Either BFileError File)
bOpenFile = Prelude.File.openFile

public export
bReadFile : String -> BIO (Either BFileError String)
bReadFile = Prelude.File.readFile

public export
chmod : String -> Int -> IO ()	
chmod f m = foreign FFI_C "chmod" (String -> Int -> IO ()) f m

public export
tmpFileName : BIO String
tmpFileName = foreign FFI_C "tmpnam" (Ptr -> IO String) null

public export
hexNum : Int -> BIO ()
hexNum num = foreign FFI_C "printf" (String -> Int -> IO ()) "%06x" num
