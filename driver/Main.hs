-- Simple driver for hermit

module Main where

import HERMIT.Driver

import System.Environment
import System.Process
import System.Exit

import Data.List (isPrefixOf)
import System.Directory (doesFileExist)

usage :: IO ()
usage = putStrLn $ unlines
        [hermit_version
        ,""
        ,"usage: hermit File.hs SCRIPTNAME"
        ,"       - OR -"
        ,"       hermit File.hs [HERMIT_ARGS] [+module_name [MOD_ARGS]]* [-- [ghc-args]]"
        ,""
        ,"examples: hermit Foo.hs Foo.hss"
        ,"          hermit Foo.hs -p6 +main:Main Foo.hss"
        ,"          hermit Foo.hs +main:Main Foo.hss resume"
        ,"          hermit Foo.hs +main:Main Foo.hss +other:Other Bar.hss"
        ,"          hermit Foo.hs -- -ddump-simpl -ddump-to-file"
        ,""
        ,"If a module name is not supplied, the module main:Main is assumed."
        ,""
        ,"HERMIT_ARGS"
        ,"  -pN         : where 0 <= N < 18 is the position in the pipeline in which HERMIT should run, 0 being at the beginning"
        ,"  -opt=MODULE : where MODULE is the module containing a HERMIT optimization plugin"
        ,""
        ,"MOD_ARGS"
        ,"  SCRIPTNAME : name of script file to run for this module"
        ,"  resume     : skip interactive mode and resume compilation after any scripts"
        ]

main :: IO ()
main = do
   args <- getArgs
   main1 args

main1 :: [String] -> IO ()
main1 [] = usage
main1 [file_nm,script_nm] = do
    e <- doesFileExist script_nm
    if e then main4 file_nm [] [("main:Main", [script_nm])] [] else usage
main1 other = main2 other

main2 (file_nm:rest) = case span (/= "--") rest of
        (args,"--":ghc_args) -> main3 file_nm args ghc_args
        (args,[])            -> main3 file_nm args []
        _ -> error "hermit internal error"

main3 file_nm args ghc_args = main4 file_nm hermit_args (sepMods margs) ghc_args
    where (hermit_args, margs) = span (not . isPrefixOf "+") args

          sepMods :: [String] -> [(String, [String])]
          sepMods [] = []
          sepMods (('+':mod_nm):rest) = (mod_nm, mod_opts) : sepMods next
            where (mod_opts, next) = span (not . isPrefixOf "+") rest

main4 file_nm hermit_args []          ghc_args = main4 file_nm hermit_args [("main:Main", [])] ghc_args
main4 file_nm hermit_args module_args ghc_args = do
        putStrLn $ "[starting " ++ hermit_version ++ " on " ++ file_nm ++ "]"
        let (pluginName, hermit_args') = getPlugin hermit_args
            cmds = file_nm : ghcFlags ++
                    [ "-fplugin=" ++ pluginName ] ++
                    [ "-fplugin-opt=" ++ pluginName ++ ":" ++ opt | opt <- hermit_args' ] ++
                    [ "-fplugin-opt=" ++ pluginName ++ ":" ++ m_nm ++ ":" ++ opt
                    | (m_nm, m_opts) <- module_args
                    , opt <- "" : m_opts
                    ] ++ ghc_args
        putStrLn $ "% ghc " ++ unwords cmds
        (_,_,_,r) <- createProcess $ proc "ghc" cmds
        ex <- waitForProcess r
        exitWith ex

getPlugin :: [String] -> (String, [String])
getPlugin = go "HERMIT" []
    where go plug flags [] = (plug, flags)
          go plug flags (f:fs) | "-opt=" `isPrefixOf` f = go (drop 5 f) flags fs
                               | otherwise              = go plug (f:flags) fs
