{-# LANGUAGE ScopedTypeVariables #-}
module HERMIT.Shell.Dictionary
    ( mkDictionary
    , addToDictionary
    , pp_dictionary
    ) where

import Data.Dynamic
import Data.List
import Data.Map (Map, fromList, toList, fromListWith)

import HERMIT.External

import HERMIT.PrettyPrinter.Common
import qualified HERMIT.PrettyPrinter.AST as AST
import qualified HERMIT.PrettyPrinter.Clean as Clean
import qualified HERMIT.PrettyPrinter.GHC as GHCPP

--------------------------------------------------------------------------

-- | A 'Dictionary' is a collection of 'Dynamic's.
--   Looking up a 'Dynamic' (via an 'ExternalName' key) returns a list, as there
--   can be multiple 'Dynamic's with the same name.
type Dictionary = Map ExternalName [Dynamic]

-- | Build a 'Data.Map' from names to 'Dynamic' values.
toDictionary :: [External] -> Dictionary
toDictionary = fromListWith (++) . map toEntry

toEntry :: External -> (ExternalName, [Dynamic])
toEntry e = (externName e, [externDyn e])

addToDictionary :: External -> Dictionary -> Dictionary
addToDictionary ex d = fromListWith (++) $ toEntry ex : toList d

-- | Create a dictionary from a list of 'External's.
mkDictionary :: [External] -> Dictionary
mkDictionary externs = toDictionary externs'
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
pp_dictionary :: Map String PrettyPrinter
pp_dictionary = fromList
    [ ("clean", Clean.pretty)
    , ("ast",   AST.pretty)
    , ("ghc",   GHCPP.pretty)
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

