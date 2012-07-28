-- Simple driver for hermit

module Main where

import System.Environment
import System.Process
import System.Exit

import Paths_hermit as P
import Data.Version

hermit_version :: String
hermit_version = "HERMIT v" ++ showVersion P.version

main :: IO ()
main = do
   args <- getArgs
   main2 args

main2 :: [String] -> IO ()
main2 [] = putStrLn $ unlines
        [hermit_version
        ,""
        ,"usage: hermit <ModuleName>.hs [args] [-- [ghc-args]]"
        ]
main2 (mod_nm:args) = case span (/= "--") args of
        (hermit_args,"--":ghc_args) -> main3 mod_nm hermit_args ghc_args
        (hermit_args,[])            -> main3 mod_nm hermit_args []
        _ -> error "hermit internal error"

main3 mod_nm hermit_args ghc_args = do
        putStrLn $ "[starting " ++ hermit_version ++ " on " ++ mod_nm ++ "]"
        let cmds =
                 [ mod_nm
                  , "-fforce-recomp"
                  , "-O2"
                  , "-dcore-lint"
                  , "-fsimple-list-literals"
--                  , "-v0"
	          , "-fplugin=HERMIT"
                  ] ++ [ "-fplugin-opt=HERMIT:main:Main:" ++ opt
                       | opt <- hermit_args
                       ] ++ ghc_args
        putStrLn $ "% ghc " ++ unwords cmds
        (_,_,_,r) <- createProcess $ proc "ghc" cmds
        ex <- waitForProcess r
        exitWith ex





