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
       "test021", "test022", "test023", "test024",
       "chez001", "chez002", "chez003", "chez004", "chez005",
       "chez006",
       "chicken001", "chicken002",
       "error001", "error002", "error003", "error004", "error005",
       "error006",
       "import001", "import002", "import003", "import004", "import005",
       "interactive001", "interactive002", "interactive003", "interactive004",
       "interactive005", "interactive006", "interactive007", "interactive008",
       "interactive009", "interactive010", "interactive011", "interactive012",
       "interface001", "interface002", "interface003", "interface004",
       "interface005", "interface006", "interface007", "interface008",
       "interface009", "interface010",
       "lazy001","lazy002",
       "linear001", "linear002", "linear003", "linear004", "linear005",
       "linear006",
       "record001", "record002",
       "reflect001",
       "perf001",
       "perror001", "perror002", "perror003", "perror004", "perror005",
       "perror006",
       "prelude001",
       "sugar001",
       "total001", "total002",
       "with001"]

chdir : String -> IO Bool
chdir dir 
    = do ok <- foreign FFI_C "chdir" (String -> IO Int) dir
         pure (ok == 0)

fail : String -> IO ()
fail err 
    = do putStrLn err
         exitWith (ExitFailure 1)

runTest : String -> String -> String -> IO Bool
runTest dir prog test
    = do chdir (dir ++ "/" ++ test)
         putStr $ dir ++ "/" ++ test ++ ": "
         system $ "sh ./run " ++ prog ++ " > output"
         Right out <- readFile "output"
               | Left err => do print err
                                pure False
         Right exp <- readFile "expected"
               | Left err => do print err
                                pure False
         if (out == exp)
            then putStrLn "success"
            else putStrLn "FAILURE"
         chdir "../.."
         pure (out == exp)

main : IO ()
main
    = do [_, ttimp, blodwen] <- getArgs
              | _ => do putStrLn "Usage: runtests [ttimp path] [blodwen path]"
         ttimps <- traverse (runTest "ttimp" ttimp) ttimpTests
         blods <- traverse (runTest "blodwen" blodwen) blodwenTests
         if (any not (ttimps ++ blods))
            then exitWith (ExitFailure 1)
            else exitWith ExitSuccess

