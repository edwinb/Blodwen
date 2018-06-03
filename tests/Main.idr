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
       "test006", "test007",
       "import001", "import002",
       "reflect001",
       "linear001", "linear002", "linear003",
       "interface001", "interface002",
       "sugar001",
       "lazy001","lazy002"]

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

