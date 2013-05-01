-- note: need to cabal install temporary to run
module Test where

import Control.Monad

import System.Directory
import System.Exit
import System.FilePath as F
import System.IO (Handle, hGetContents, hPutStrLn, hClose)
import System.IO.Temp (withTempFile)
import System.Process hiding (runCommand)

import HERMIT.Driver

type Test = (FilePath, FilePath, FilePath)

-- subdirectory names
golden, dump :: String
golden = "golden"
dump = "dump"

tests :: [Test]
tests = [ ("concatVanishes", "Flatten.hs", "Flatten.hss")
        , ("concatVanishes", "QSort.hs"  , "QSort.hss"  )
        , ("concatVanishes", "Rev.hs"    , "Rev.hss"    )
        , ("evaluation"    , "Eval.hs"   , "Eval.hss"   )
        , ("factorial"     , "Fac.hs"    , "Fac.hss"    )
        -- broken due to Core Parser: , ("fib-stream"    , "Fib.hs"    , "Fib.hss"    )
        , ("fib-tuple"     , "Fib.hs"    , "Fib.hss"    )
        , ("flatten"       , "Flatten.hs", "Flatten.hss")
        , ("hanoi"         , "Hanoi.hs"  , "Hanoi.hss"  )
        , ("last"          , "Last.hs"   , "Last.hss"   )
        , ("map"           , "Map.hs"    , "Map.hss"    )
        , ("mean"          , "Mean.hs"   , "Mean.hss"   )
        -- requires Criterion: , ("nub"           , "Nub.hs"    , "Nub.hss"    )
        , ("qsort"         , "QSort.hs"  , "QSort.hss"  )
        , ("reverse"       , "Reverse.hs", "Reverse.hss")
        ]

fixName :: FilePath -> FilePath
fixName = map (\c -> if c == '.' then '_' else c)

mkTestScript :: Handle -> FilePath -> IO ()
mkTestScript h hss = do
    hPutStrLn h
        $ unlines [ "set-auto-corelint True"
                  , "set-pp-expr-type Show"
                  , "set-fail-hard True"
                  , "load \"" ++ hss ++ "\""
                  , "top ; down"
                  , "display" -- all the bindings
                  , "resume" ]
    hClose h

main :: IO ()
main = do
    pwd <- getCurrentDirectory

    forM_ tests $ \ (dir, hs, hss) -> do
        withTempFile pwd "Test.hss" $ \ fp h -> do
            putStr $ "Running " ++ dir </> hs ++ " - "

            let fixed = fixName (concat [dir, "_", hs, "_", hss])
                gfile = pwd </> golden </> fixed <.> "ref"
                desired = pwd </> dump </> fixed <.> "dump"
                pathp = ".." </> "examples" </> dir

            b <- doesFileExist gfile
            dfile <- if not b
                     then do putStrLn $ "Reference file (" ++ gfile ++ ") does not exist. Creating!"
                             return gfile
                     else return desired

            mkTestScript h hss

            let cmd = unwords $ [ "(", "cd", pathp, ";", "ghc" , hs ] ++ ghcFlags ++
                                [ "-fplugin=HERMIT"
                                , "-fplugin-opt=HERMIT:main:Main:" ++ fp -- made by mkTestScript
                                , "-v0"
                                , "&> " ++ dfile
                                , ")" ]
                diff = unwords [ "diff", "-b", "-U 5", gfile, dfile ]

            -- putStrLn cmd
            (_,_,_,rHermit) <- createProcess $ shell cmd
            exHermit <- waitForProcess rHermit

            case exHermit of
                ExitFailure i -> putStrLn $ "HERMIT failed with code: " ++ show i
                ExitSuccess   -> return ()

            -- putStrLn diff
            (_,mbStdoutH,_,rDiff) <- createProcess $ (shell diff) { std_out = CreatePipe }
            exDiff <- waitForProcess rDiff
            case exDiff of
                ExitFailure i | i > 1 -> putStrLn $ "diff failed with code: " ++ show i
                _ -> maybe (putStrLn "error: no stdout!")
                           (\hDiff -> do output <- hGetContents hDiff
                                         if null output
                                         then putStrLn "passed."
                                         else do putStrLn "failed:"
                                                 putStrLn output)
                           mbStdoutH
