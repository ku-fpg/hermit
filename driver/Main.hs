{-# LANGUAGE ViewPatterns #-}

module Main where

import HERMIT.Driver

import System.Environment
import System.Process
import System.Exit

import Data.List (isPrefixOf, partition)
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
        ,"          hermit Foo.hs -p6 +Main Foo.hss"
        ,"          hermit Foo.hs +Main Foo.hss resume"
        ,"          hermit Foo.hs +Main Foo.hss +Other.Module.Name Bar.hss"
        ,"          hermit Foo.hs -- -ddump-simpl -ddump-to-file"
        ,""
        ,"A * may be used for the module name. * matches any module."
        ,"If a module name is not supplied, * is assumed."
        ,""
        ,"HERMIT_ARGS"
        ,"  -opt=MODULE : where MODULE is the module containing a HERMIT optimization plugin"
        ,"  -vN         : controls verbosity, where N is one of the following values:"
        ,"                  0 : suppress HERMIT messages, pass -v0 to GHC"
        ,"                  1 : suppress HERMIT messages"
        ,"                  2 : pass -v0 to GHC"
        ,"                  3 : (default) display all HERMIT and GHC messages"
        ,""
        ,"MOD_ARGS"
        ,"  SCRIPTNAME : name of script file to run for this module"
        ,"  resume     : skip interactive mode and resume compilation after any scripts"
        ]

main :: IO ()
main = getArgs >>= main1

main1 :: [String] -> IO ()
main1 [] = usage
main1 args@(file_nm:script_nm:rest) = do
    e <- doesFileExist script_nm
    if e && (not (any (isPrefixOf "+") rest)) 
        then main4 file_nm [] [("*", script_nm:rest)] [] 
        else main2 args
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

main4 file_nm hermit_args []          ghc_args = main4 file_nm hermit_args [("*", [])] ghc_args
main4 file_nm hermit_args module_args ghc_args = do
        putStrLn $ "[starting " ++ hermit_version ++ " on " ++ file_nm ++ "]"
        let (pluginName, hermit_args') = getPlugin hermit_args
            cmds = file_nm : ghcFlags ++
                    [ "-fplugin=" ++ pluginName ] ++
                    [ "-fplugin-opt=" ++ pluginName ++ ":" ++ opt | opt <- hermit_args' ] ++
                    [ "-fplugin-opt=" ++ pluginName ++ ":" ++ m_nm ++ ":" ++ opt
                    | (m_nm, m_opts) <- module_args
                    , opt <- "" : m_opts
                    ] ++ extraGHCArgs hermit_args' ++ ghc_args
        putStrLn $ "% ghc " ++ unwords cmds
        (_,_,_,r) <- createProcess $ proc "ghc" cmds
        ex <- waitForProcess r
        exitWith ex

getPlugin :: [String] -> (String, [String])
getPlugin = go "HERMIT" []
    where go plug flags [] = (plug, reverse flags) -- flag ordering is important here
          go plug flags (f:fs) | "-opt=" `isPrefixOf` f = go (drop 5 f) flags fs
                               | otherwise              = go plug (f:flags) fs

-- | See if the given HERMIT args imply any additional GHC args
extraGHCArgs :: [String] -> [String]
extraGHCArgs (matchArgs (`elem` ["-v0","-v2"]) -> Just (_,r)) = "-v0" : extraGHCArgs r
extraGHCArgs _ = []

matchArgs :: (String -> Bool) -> [String] -> Maybe ([String], [String])
matchArgs p args = case partition p args of
                    ([],_) -> Nothing
                    (as,r) -> Just (as,r)
