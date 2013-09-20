{-# LANGUAGE ScopedTypeVariables #-}
module HERMIT.Shell.Dictionary
    ( mkDict
    , pp_dictionary
    ) where

import Data.List
import Data.Map (Map, fromList, toList)

import HERMIT.Kure
import HERMIT.External

import HERMIT.PrettyPrinter.Common
import qualified HERMIT.PrettyPrinter.AST as AST
import qualified HERMIT.PrettyPrinter.Clean as Clean
import qualified HERMIT.PrettyPrinter.GHC as GHCPP

--------------------------------------------------------------------------

-- | Create a dictionary from a list of 'External's.
mkDict :: [External] -> Dictionary
mkDict externs = toDictionary externs'
  where
        msg = layoutTxt 60 (map (show . fst) dictionaryOfTags)
        externs' = externs ++
                [ external "help" (help_command externs' "help")
                    [ "(this message)" ] .+ Query .+ Shell
                , external "help" (help_command externs')
                    ([ "help <command>|<category>|categories|all|<search-string>"
                     , "Displays help about a command, or all commands in a category."
                     , "Multiple items may match."
                     , ""
                     , "Categories: " ++ head msg
                     ] ++ map ("            " ++) (tail msg))  .+ Query .+ Shell
                ]

--------------------------------------------------------------------------

-- | The pretty-printing dictionaries.
pp_dictionary :: Map String (PrettyH CoreTC)
pp_dictionary = fromList
        [ ("clean",  Clean.ppCoreTC)
        , ("ast",    AST.ppCoreTC)
        , ("ghc",    GHCPP.ppCoreTC)
        ]

--------------------------------------------------------------------------

make_help :: [External] -> [String]
make_help = concatMap snd . toList . toHelp

help_command :: [External] -> String -> String
help_command exts m
        | [(ct :: CmdTag,"")] <- reads m
        = unlines $ make_help $ filter (tagMatch ct) exts
help_command exts "all"
        = unlines $ make_help exts
help_command _ "categories" = unlines $
                [ "Categories" ] ++
                [ "----------" ] ++
                [ txt ++ " " ++ replicate (16 - length txt) '.' ++ " " ++ desc
                | (cmd,desc) <- dictionaryOfTags
                , let txt = show cmd
                ]

help_command exts m = unlines $ make_help $ pathPrefix m
    where pathPrefix p = filter (isInfixOf p . externName) exts

layoutTxt :: Int -> [String] -> [String]
layoutTxt n (w1:w2:ws) | length w1 + length w2 >= n = w1 : layoutTxt n (w2:ws)
                       | otherwise = layoutTxt n ((w1 ++ " " ++ w2) : ws)
layoutTxt _ other = other

--------------------------------------------------------------------------

