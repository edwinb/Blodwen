module Main

import System

%default covering

ttimpTests : List String
ttimpTests 
    = ["test001", "test002", "test003", "test004", "test005",
       "test006", "test007", "test008", "test009",
       "case001",
       "linear001", "linear002", "linear003",
       "perf001"]

blodwenTests : List String
blodwenTests
    = ["test001", "test002", "test003", "test004", "test005",
       "test006", "test007", "test008", "test009", "test010",
       "test011", "test012", "test013", "test014", "test015",
       "test016", "test017", "test018", "test019", "test020",
       "error001", "error002", "error003", "error004",
       "chez001", "chez002", "chez003", "chez004", "chez005",
       "chez006",
       "chicken001", "chicken002",
       "import001", "import002", "import003",
       "reflect001",
       "linear001", "linear002", "linear003", "linear004",
       "interface001", "interface002", "interface003", "interface004",
       "interface005", "interface006", "interface007", "interface008",
       "interface009",
       "sugar001",
       "lazy001","lazy002",
       "perf001",
       "prelude001"]

chdir : String -> IO Bool
chdir dir 
    = do ok <- foreign FFI_C "chdir" (String -> IO Int) dir
         pure (ok == 0)

fail : String -> IO ()
fail err 
    = do putStrLn err
         exitWith (ExitFailure 1)

runTest : String -> String -> String -> IO ()
runTest dir prog test
    = do chdir (dir ++ "/" ++ test)
         putStr $ dir ++ "/" ++ test ++ ": "
         system $ "sh ./run " ++ prog ++ " > output"
         Right out <- readFile "output"
               | Left err => fail (show err)
         Right exp <- readFile "expected"
               | Left err => fail (show err)
         if (out == exp)
            then putStrLn "success"
            else putStrLn "FAILURE"
         chdir "../.."
         pure ()

main : IO ()
main
    = do [_, ttimp, blodwen] <- getArgs
              | _ => do putStrLn "Usage: runtests [ttimp path] [blodwen path]"
         traverse (runTest "ttimp" ttimp) ttimpTests
         traverse (runTest "blodwen" blodwen) blodwenTests
         pure ()

