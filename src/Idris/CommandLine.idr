module Idris.CommandLine

import Data.Vect

%default total

public export
data CLOpt
  = CheckOnly
  | ExecFn String
  | SetCG String
  | NoPrelude
  | Version
  | Help
  | Quiet
  | InputFile String

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
           MkOpt ["--no-prelude", "-q"] [] [NoPrelude]
              (Just "Don't implicitly import Prelude"),
           MkOpt ["--codegen"] ["backend"] (\f => [SetCG f])
              (Just "Set code generator (default chez)"),

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
                optshow ++ pack (List.replicate (minus 20 (length optshow)) ' ')
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

export covering
getOpts : IO (Either String (List CLOpt))
getOpts = do (_ :: opts) <- getArgs
                 | pure (Left "Invalid command line")
             pure $ parseOpts options opts

