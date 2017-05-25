module Main

import Core.TT
import Parser.Raw

main : IO ()
main = do putStr ": "
          x <- getLine
          case runParser x name of
               Left err => do putStrLn "bad input"
                              main
               Right ok => do print ok
                              main

