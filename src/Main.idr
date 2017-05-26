module Main

import Core.TT
import Parser.Raw

main : IO ()
main = do putStr ": "
          x <- getLine
          case runParser x raw of
               Left err => do putStrLn "bad input"
                              printLn err
                              main
               Right ok => do printLn "parsed"
                              main

