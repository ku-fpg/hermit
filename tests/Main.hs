{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ViewPatterns #-}
module Main (main) where

import Constants (hiVersion)
import Control.Monad.Compat

import Data.Char (isSpace)
import Data.List.Compat
import Data.Maybe (listToMaybe)

import GHC.Paths (ghc)

import HERMIT.Driver

import Prelude.Compat

import System.Directory
import System.FilePath as F
import System.Info (arch, os)
import System.IO
import System.IO.Temp (withSystemTempFile)
import System.Process

import Test.Tasty (TestTree, TestName, defaultMain, testGroup)
import Test.Tasty.Golden (goldenVsFileDiff)

type HermitTestArgs = (FilePath, FilePath, FilePath, [String])

main :: IO ()
main = defaultMain hermitTests

hermitTests :: TestTree
hermitTests = testGroup "HERMIT tests" $ map mkHermitTest testArgs

-- subdirectory names
golden, dump, rootDir, examples :: FilePath
golden   = "golden" </> "golden-ghc-" ++ show hiVersion
dump     = "dump"
rootDir  = "tests"
examples = "examples"

testArgs :: [HermitTestArgs]
testArgs = [ ("concatVanishes", "Flatten.hs", "Flatten.hss", ["-safety=unsafe"])
        , ("concatVanishes", "QSort.hs"  , "QSort.hss"  , ["-safety=unsafe"])
        , ("concatVanishes", "Rev.hs"    , "Rev.hss"    , ["-safety=unsafe"])
        , ("evaluation"    , "Eval.hs"   , "Eval.hss"   , [])
#if __GLASGOW_HASKELL__ < 710
        -- broken on GHC 7.10 due to not satisfying the let/app invariant. I should probably fix this.
        , ("factorial"     , "Fac.hs"    , "Fac.hss"    , [])
#endif
        -- broken due to Core Parser: , ("fib-stream"    , "Fib.hs"    , "Fib.hss"    )
        , ("fib-tuple"     , "Fib.hs"    , "Fib.hss"    , [])
        , ("flatten"       , "Flatten.hs", "Flatten.hec", ["-safety=unsafe"])
        -- for some reason loops in testsuite but not normally: , ("hanoi"         , "Hanoi.hs"  , "Hanoi.hss"  )
        , ("last"          , "Last.hs"   , "Last.hss"   , ["-safety=unsafe"])
        , ("last"          , "Last.hs"   , "NewLast.hss", ["-safety=strict"])
        -- broken due to Core Parser: , ("map"           , "Map.hs"    , "Map.hss"    )
        , ("mean"          , "Mean.hs"   , "Mean.hss"   , [])
        -- TODO: re-enable once fixed , ("nub"           , "Nub.hs"    , "Nub.hss"    , [])
        , ("qsort"         , "QSort.hs"  , "QSort.hss"  , [])
        , ("reverse"       , "Reverse.hs", "Reverse.hss", ["-safety=unsafe"])
        , ("new_reverse"   , "Reverse.hs", "Reverse.hec", [])
        ]

fixName :: FilePath -> FilePath
fixName = map (\c -> if c == '.' then '_' else c)

mkTestScript :: Handle -> FilePath -> IO ()
mkTestScript h hss = do
    hPutStrLn h
        $ unlines [ "set-auto-corelint True"
                  , "set-pp-type Show"
                  , "set-fail-hard True"
                  , "load-and-run \"" ++ hss ++ "\""
                  , "top ; prog"
                  , "display" -- all the bindings
                  , "show-lemmas"
                  , "resume" ]
    hClose h

-- | Get the path to the sandbox database if any
-- Taken from hoogle-index (by Ben Gamari, under BSD3)
getSandboxDb :: IO (Maybe FilePath)
getSandboxDb = do
  dir <- getCurrentDirectory
  let f = dir </> "cabal.sandbox.config"
  ex <- doesFileExist f
  if ex
    then
      (listToMaybe .
       map ((</> archOSCompilerConf) .
            dropFileName .
            dropWhile isSpace .
            tail .
            dropWhile (/= ':')) .
       filter (isPrefixOf "package-db") .
       lines) <$> readFile f
    else return Nothing
  where
    archOSCompilerConf :: String
    archOSCompilerConf = intercalate "-" [arch, theOS, takeFileName ghc, "packages.conf.d"]

    theOS :: String
#if defined(darwin_HOST_OS)
    theOS = "osx" -- System.Info.os gives "darwin", which isn't what is actually
                  -- used, for some silly reason
#else
    theOS = os
#endif

mkHermitTest :: HermitTestArgs -> TestTree
mkHermitTest (dir, hs, hss, extraFlags) =
    goldenVsFileDiff testName diff gfile dfile hermitOutput
  where
    testName :: TestName
    testName = dir </> hs

    fixed, gfile, dfile, pathp :: FilePath
    fixed = fixName (concat [dir, "_", hs, "_", hss])
    gfile = rootDir  </> golden </> fixed <.> "ref"
    dfile = rootDir  </> dump   </> fixed <.> "dump"
    pathp = examples </> dir

    diff :: FilePath -> FilePath -> [String]
    diff ref new = ["diff", "-b", "-U 5", ref, new]

    -- For some incredibly bizarre reason, HERMIT's output can be have different
    -- line orderings depending on if it's been run once before. As far as I can
    -- tell, this is due to the presence of object (.o) and interface (.hi) files.
    -- Wat.
    --
    -- Luckily, removing any object or interface before running HERMIT seems to
    -- provide a guarantee that HERMIT's output will be the same on subsequent runs.
    cleanObjectFiles :: IO ()
    cleanObjectFiles = do
        files <- getDirectoryContents pathp
        forM_ files $ \file ->
            when (takeExtension file `elem` [".o", ".hi"]) $
               removeFile $ pathp </> file

    hermitOutput :: IO ()
    hermitOutput = do
        cleanObjectFiles
        mbDb <- getSandboxDb
        createDirectoryIfMissing True (dropFileName gfile)

        let dbFlags :: String
            dbFlags | Just db <- mbDb
                    = unwords ["-no-user-package-db", "-package-db", db]
                    | otherwise = ""

        withSystemTempFile "Test.hss" $ \ fp h -> do
            mkTestScript h hss

            let cmd :: String
                cmd = unwords $    [ "("
                                   , "cd"
                                   , pathp
                                   , ";"
                                   , ghc
                                   , dbFlags
                                   , hs
                                   , "-w" -- Disable all warnings
                                   ]
                                ++ ghcFlags
                                ++ [ "-fplugin=HERMIT"
                                   , "-fplugin-opt=HERMIT:Main:" ++ fp -- made by mkTestScript
                                   , "-v0"
                                   ]
                                ++ [ "-fplugin-opt=HERMIT:Main:" ++ f | f <- extraFlags]
                                ++ [ ")" ]

            -- Adding a &> dfile redirect in cmd causes the call to GHC to not block
            -- until the compiler is finished (on Linux, not OSX). So we do the Haskell
            -- equivalent here by opening our own file.
            fh <- openFile dfile WriteMode
            -- putStrLn cmd
            (_,_,_,rHermit) <- createProcess $ (shell cmd) { std_out = UseHandle fh, std_err = UseHandle fh }
            _ <- waitForProcess rHermit

            -- Ensure that the golden file exists prior to calling diff
            goldenExists <- doesFileExist gfile
            unless goldenExists $ copyFile dfile gfile
