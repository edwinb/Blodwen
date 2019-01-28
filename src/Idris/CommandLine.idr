module Idris.CommandLine

import Data.Vect

import CompilerRuntime

%default total

public export
data PkgCommand
      = Build
      | Install
      | REPL


export
Show PkgCommand where
  show Build = "--build"
  show Install = "--install"
  show REPL = "--repl"

public export
data CLOpt
  = CheckOnly
  | ExecFn String
  | SetCG String
  | NoPrelude
  | ShowPrefix
  | Version
  | Help
  | Quiet
  | PkgPath String
  | Package PkgCommand String
  | InputFile String
  | IdeMode
  | BlodwenPaths

ActType : List String -> Type
ActType [] = List CLOpt
ActType (a :: as) = String -> ActType as

record OptDesc where
  constructor MkOpt
  flags : List String
  argdescs : List String
  action : ActType argdescs
  help : Maybe String

options : List OptDesc
options = [MkOpt ["--check", "-c"] [] [CheckOnly]
              (Just "Exit after checking source file"),
           MkOpt ["--exec", "-x"] ["name"] (\f => [ExecFn f, Quiet])
              (Just "Execute function after checking source file"),
           MkOpt ["--no-prelude"] [] [NoPrelude]
              (Just "Don't implicitly import Prelude"),
           MkOpt ["--codegen", "--cg"] ["backend"] (\f => [SetCG f])
              (Just "Set code generator (default chez)"),
           MkOpt ["--package", "-p"] ["package"] (\f => [PkgPath f])
              (Just "Add a package as a dependency"),

           MkOpt ["--ide-mode"] [] [IdeMode]
              (Just "Run the REPL with machine-readable syntax"),

           MkOpt ["--prefix"] [] [ShowPrefix]
              (Just "Show installation prefix"),
           MkOpt ["--paths"] [] [BlodwenPaths]
              (Just "Show paths"),
           MkOpt ["--build"] ["package file"] (\f => [Package Build f])
              (Just "Build modules/executable for the given package"),
           MkOpt ["--install"] ["package file"] (\f => [Package Install f])
              (Just "Install the given package"),

           MkOpt ["--quiet", "-q"] [] [Quiet]
              (Just "Quiet mode; display fewer messages"),
           MkOpt ["--version", "-v"] [] [Version]
              (Just "Display version string"),
           MkOpt ["--help", "-h", "-?"] [] [Help]
              (Just "Display help text")
           ]

optUsage : OptDesc -> String
optUsage d
    = maybe "" -- Don't show anything if there's no help string (that means
               -- it's an internal option)
        (\h =>
            let optshow = showSep "," (flags d) ++ " " ++
                    showSep " " (map (\x => "<" ++ x ++ ">") (argdescs d)) in
                optshow ++ pack (List.replicate (minus 26 (length optshow)) ' ')
                ++ h ++ "\n") (help d)
  where
    showSep : String -> List String -> String
    showSep sep [] = ""
    showSep sep [x] = x
    showSep sep (x :: xs) = x ++ sep ++ showSep sep xs

export
version : String
version = "0.1"

export
versionMsg : String
versionMsg = "Blodwen, a prototype successor to Idris, version " ++ version

export
usage : String
usage = versionMsg ++ "\n" ++
        "Usage: blodwen [options] [input file]\n\n" ++
        "Available options:\n" ++
        concatMap (\u => "  " ++ optUsage u) options

processArgs : String -> (args : List String) -> List String -> ActType args ->
              Either String (List CLOpt, List String)
processArgs flag [] xs f = Right (f, xs)
processArgs flag (a :: as) [] f
    = Left $ "Missing argument <" ++ a ++ "> for flag " ++ flag
processArgs flag (a :: as) (x :: xs) f
    = processArgs flag as xs (f x)

matchFlag : (d : OptDesc) -> List String ->
            Either String (Maybe (List CLOpt, List String))
matchFlag d [] = Right Nothing -- Nothing left to match
matchFlag d (x :: xs)
    = if x `elem` flags d
         then do args <- processArgs x (argdescs d) xs (action d)
                 Right (Just args)
         else Right Nothing

findMatch : List OptDesc -> List String ->
            Either String (List CLOpt, List String)
findMatch [] [] = Right ([], [])
findMatch [] (f :: args) = Right ([InputFile f], args)
findMatch (d :: ds) args
    = case !(matchFlag d args) of
           Nothing => findMatch ds args
           Just res => Right res

parseOpts : List OptDesc -> List String -> Either String (List CLOpt)
parseOpts opts [] = Right []
parseOpts opts args
   = do (cl, rest) <- findMatch opts args
        cls <- assert_total (parseOpts opts rest) -- 'rest' smaller than 'args'
        pure (cl ++ cls)

export
getOpts : List String -> Either String (List CLOpt)
getOpts opts = parseOpts options opts


export covering
getCmdOpts : BIO (Either String (List CLOpt))
getCmdOpts = do (_ :: opts) <- getArgs
                    | pure (Left "Invalid command line")
                pure $ getOpts opts
