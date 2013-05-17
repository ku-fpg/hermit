{-# LANGUAGE GADTs, ScopedTypeVariables #-}

module Language.HERMIT.Dictionary
    ( -- * The HERMIT Dictionary
      -- | This is the main namespace. Things tend to be untyped, because the API is accessed via (untyped) names.
      Dictionary
    , externals
    , mkDict
    , pp_dictionary
    , bashR
    ) where

-- import Data.Default (def)
import Data.Dynamic
import Data.List
import Data.Map (Map, fromList, toList)

import Language.HERMIT.Core
import Language.HERMIT.Kure
import Language.HERMIT.External

import qualified Language.HERMIT.Primitive.AlphaConversion as Alpha
import qualified Language.HERMIT.Primitive.Debug as Debug
import qualified Language.HERMIT.Primitive.FixPoint as FixPoint
import qualified Language.HERMIT.Primitive.Fold as Fold
import qualified Language.HERMIT.Primitive.GHC as GHC
import qualified Language.HERMIT.Primitive.Inline as Inline
import qualified Language.HERMIT.Primitive.Kure as Kure
import qualified Language.HERMIT.Primitive.Local as Local
import qualified Language.HERMIT.Primitive.Navigation as Navigation
import qualified Language.HERMIT.Primitive.New as New
import qualified Language.HERMIT.Primitive.Unfold as Unfold

import Language.HERMIT.PrettyPrinter.Common
import qualified Language.HERMIT.PrettyPrinter.AST as AST
import qualified Language.HERMIT.PrettyPrinter.Clean as Clean
import qualified Language.HERMIT.PrettyPrinter.GHC as GHCPP

--------------------------------------------------------------------------

-- | A 'Dictionary' is a collection of 'Dynamic's.
--   Looking up a 'Dynamic' (via a 'String' key) returns a list, as there can be multiple 'Dynamic's with the same name.
type Dictionary = Map String [Dynamic]

-- | List of all 'External's provided by HERMIT.
externals :: [External]
externals =
       Alpha.externals
    ++ Debug.externals
    ++ FixPoint.externals
    ++ Fold.externals
    ++ GHC.externals
    ++ Inline.externals
    ++ Kure.externals
    ++ Local.externals
    ++ Navigation.externals
    ++ New.externals
    ++ Unfold.externals

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
                     , "displays help about a command or category."
                     , "Multiple items may match."
                     , ""
                     , "categories: " ++ head msg
                     ] ++ map ("            " ++) (tail msg))  .+ Query .+ Shell
                -- Runs every command matching the tag predicate with innermostR (fix point anybuR),
                -- Only fails if all of them fail the first time.
                , external "bash" (bashR externs) (bashHelp externs) .+ Eval .+ Deep .+ Loop
                ]

--------------------------------------------------------------------------

-- | The pretty-printing dictionaries.
pp_dictionary :: Map String (PrettyOptions -> PrettyH Core)
pp_dictionary = fromList
        [ ("clean",  Clean.corePrettyH)
        , ("ast",    AST.corePrettyH)
        , ("ghc",    GHCPP.corePrettyH)
        ]

{-
-- (This isn't used anywhere currently.)
-- | Each pretty printer can suggest some options
pp_opt_dictionary :: Map String PrettyOptions
pp_opt_dictionary = fromList
        [ ("clean", def)
        , ("ast",  def)
        , ("ghc",  def)
        ]
-}

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
                [ "categories" ] ++
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

bashPredicate :: CmdTag
bashPredicate = Bash

bashR :: [External] -> RewriteH Core
bashR = setFailMsg "bashR: nothing to do."
      . innermostR . orR . map snd . matchingExternals bashPredicate

bashHelp :: [External] -> [String]
bashHelp exts =
    "Iteratively apply the following rewrites until nothing changes:"
    : [ externName e | (e,_ :: RewriteH Core) <- matchingExternals bashPredicate exts ]

--------------------------------------------------------------------------

