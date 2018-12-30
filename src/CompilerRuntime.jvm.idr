module CompilerRuntime

import Java.Lang
import public Control.IOExcept
import public IdrisJvm.IO
import public IdrisJvm.File
import public IdrisJvm.System
import public IdrisJvm.Data.Buffer
import public Data.IORef

public export
BIO : Type -> Type
BIO = JVM_IO

public export
BIORef : Type -> Type
BIORef = IdrisJvm.FFI.IORef

public export
BIOExcept : Type -> Type -> Type
BIOExcept = IOExcept' FFI_JVM

public export
tmpFileName : BIO String
tmpFileName = getTemporaryFileName

public export
hexNum : Int -> BIO ()
hexNum num = print $ JavaString.format "%06x" !(listToArray [the Object $ believe_me $ JInteger.valueOf num])



public export
bChangeDir : String -> BIO Bool
bChangeDir = IdrisJvm.File.changeDir

public export
bPrintLn : Show ty => ty -> BIO ()
bPrintLn = IdrisJvm.IO.printLn

public export
bPutChar : Char -> BIO () 
bPutChar = IdrisJvm.IO.putChar

public export
bGetChar : BIO Char
bGetChar = IdrisJvm.IO.getChar

public export
BFile : Type
BFile = IdrisJvm.File.File

public export
BFileError : Type
BFileError = IdrisJvm.File.FileError

public export
cannotOpenFile : String -> BFileError
cannotOpenFile fn = believe_me (unableToReadFile fn)

public export
bOpenFile : (f : String) -> (m : Mode) -> BIO (Either BFileError File)
bOpenFile = IdrisJvm.File.openFile

public export
bReadFile : String -> BIO (Either BFileError String)
bReadFile = IdrisJvm.File.readFile

public export
chmod : String -> Int -> BIO ()
chmod = IdrisJvm.File.chmod
