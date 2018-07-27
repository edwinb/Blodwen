module Core.Directory

import Core.Context
import Core.Options
import Core.Core
import Core.Name

import System.Info

%default total

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
    
firstAvailable : annot -> List String -> List String -> Core annot String
firstAvailable loc ns [] = throw (ModuleNotFound loc ns)
firstAvailable loc ns (f :: fs)
    = do Right ok <- coreLift $ openFile f Read
               | Left err => firstAvailable loc ns fs
         coreLift $ closeFile ok
         pure f

-- Given a namespace, return the full path to the checked module, 
-- looking first in the build directory then in the extra_dirs
export
nsToPath : {auto c : Ref Ctxt Defs} ->
           annot -> List String -> Core annot String
nsToPath loc ns
    = do d <- getDirs
         let fnameBase = showSep (cast sep) (reverse ns)
         let fs = map (\p => p ++ cast sep ++ fnameBase ++ ".ttc")
                      (build_dir d :: extra_dirs d)
         firstAvailable loc ns fs

-- Given a namespace, return the full path to the source module (if it
-- exists in the working directory)
export
nsToSource : {auto c : Ref Ctxt Defs} ->
             annot -> List String -> Core annot String
nsToSource loc ns
    = do d <- getDirs
         let fnameBase = showSep (cast sep) (reverse ns)
         let fs = map (\ext => fnameBase ++ ext)
                      [".blod", ".idr", ".lidr"]
         firstAvailable loc ns fs

-- Given a filename in the working directory, return the correct
-- namespace for it
export
pathToNS : String -> List String
pathToNS fname
    = case span (/=sep) fname of
           (end, "") => [dropExtension end]
           (mod, rest) => assert_total (pathToNS (strTail rest)) ++ [mod]

-- Create subdirectories, if they don't exist
mkdirs : List String -> IO (Either FileError ())
mkdirs [] = pure (Right ())
mkdirs (d :: ds)
    = do ok <- changeDir d
         if ok
            then do mkdirs ds
                    changeDir ".."
                    pure (Right ())
            else do Right _ <- createDir d
                        | Left err => pure (Left err)
                    ok <- changeDir d
                    mkdirs ds
                    changeDir ".."
                    pure (Right ())

-- Given a namespace (i.e. a module name), make the build directory for the 
-- corresponding ttc file
export
makeBuildDirectory : {auto c : Ref Ctxt Defs} ->
                     List String -> Core annot ()
makeBuildDirectory ns
    = do d <- getDirs
         let bdir = build_dir d
         let ndirs = case ns of
                          [] => []
                          (n :: ns) => ns -- first item is file name
         let fname = showSep (cast sep) (reverse ndirs)
         Right _ <- coreLift $ mkdirs (build_dir d :: reverse ndirs)
            | Left err => throw (FileErr (bdir ++ cast sep ++ fname) err)
         pure ()

-- Given a source file, return the name of the ttc file to generate
export
getTTCFileName : {auto c : Ref Ctxt Defs} -> String -> Core annot String
getTTCFileName inp 
    = do ns <- getNS
         d <- getDirs
         let bdir = build_dir d
         pure $ bdir ++ cast sep ++ dropExtension inp ++ ".ttc"

-- Given a root executable name, return the name in the build directory
export
getExecFileName : {auto c : Ref Ctxt Defs} -> String -> Core annot String
getExecFileName efile
    = do d <- getDirs
         pure $ build_dir d ++ cast sep ++ efile
