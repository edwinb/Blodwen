module Main

import Core.TT
import Core.Evaluate
import Parser.Raw

main : IO ()
main = do putStrLn "Parsing"
          Right res <- parseFile "test.tt" prog
                | Left err => printLn err
          putStrLn "Parsed OK"
          putStrLn (showSep "\n" (map show res))

