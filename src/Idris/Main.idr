module Main

import Core.Core

import Idris.Syntax
import Idris.ProcessIdr

stMain : Core FC ()
stMain = coreLift $ putStrLn "Nothing happens"

main : IO ()
main = do putStrLn "Welcome to Blodwen. Good luck."
          coreRun stMain
               (\err : Error _ => putStrLn ("Uncaught error: " ++ show err))
               (\res => pure ())

