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
golden = "golden"
dump = "dump"

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
        $ unlines [ "load \"" ++ hss ++ "\""
                  , "top ; down"
                  , "display" -- all the bindings
                  , "resume" ]
    hClose h

main = do
    pwd <- getCurrentDirectory

    forM_ tests $ \ (dir, hs, hss) -> do
        withTempFile pwd "Test.hss" $ \ fp h -> do
            putStr $ "Running " ++ dir ++ " - "

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
            (_,_,_,r) <- createProcess $ shell cmd
            ex <- waitForProcess r

            case ex of
                ExitFailure i -> putStrLn $ "HERMIT failed with code: " ++ show i
                ExitSuccess   -> do
                    -- putStrLn diff
                    (_,mbStdoutH,_,r) <- createProcess $ (shell diff) { std_out = CreatePipe }
                    ex <- waitForProcess r
                    case ex of
                        ExitFailure i | i > 1 -> putStrLn $ "diff failed with code: " ++ show i
                        _ -> maybe (putStrLn "error: no stdout!")
                                   (\h -> do output <- hGetContents h
                                             if null output
                                             then putStrLn "passed."
                                             else do putStrLn "failed:"
                                                     putStrLn output)
                                   mbStdoutH