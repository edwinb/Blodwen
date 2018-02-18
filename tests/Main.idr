module Main

import System

%default covering

tests : List String
tests = ["test001", "test002", "test003", "test004", "test005",
         "test006", "test007", "test008",
         "case001",
         "linear001", "linear002",
         "perf001"]

chdir : String -> IO Bool
chdir dir 
    = do ok <- foreign FFI_C "chdir" (String -> IO Int) dir
         pure (ok == 0)

fail : String -> IO ()
fail err 
    = do putStrLn err
         exitWith (ExitFailure 1)

runTest : String -> IO ()
runTest test
    = do chdir test
         putStr $ test ++ ": "
         system "sh ./run > output"
         Right out <- readFile "output"
               | Left err => fail (show err)
         Right exp <- readFile "expected"
               | Left err => fail (show err)
         if (out == exp)
            then putStrLn "success"
            else putStrLn "FAILURE"
         chdir ".."
         pure ()

main : IO ()
main
    = do chdir "tests"
         traverse runTest tests
         pure ()
