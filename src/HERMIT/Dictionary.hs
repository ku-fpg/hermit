{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Dictionary
    ( -- * The HERMIT Dictionary
      -- | This is the main namespace. Things tend to be untyped, because the API is accessed via (untyped) names.
      Dictionary
    , externals
    , mkDict
    , pp_dictionary
    , bashR
    , bashDebugR
    ) where

import Control.Arrow

import Data.List
import Data.Map (Map, fromList, toList)

import HERMIT.Kure
import HERMIT.External

import qualified HERMIT.Primitive.AlphaConversion as Alpha
import qualified HERMIT.Primitive.Composite as Composite
import qualified HERMIT.Primitive.Debug as Debug
import qualified HERMIT.Primitive.FixPoint as FixPoint
import qualified HERMIT.Primitive.Fold as Fold
import qualified HERMIT.Primitive.Function as Function
import qualified HERMIT.Primitive.GHC as GHC
import qualified HERMIT.Primitive.Inline as Inline
import qualified HERMIT.Primitive.Kure as Kure
import qualified HERMIT.Primitive.Local as Local
import qualified HERMIT.Primitive.Navigation as Navigation
import qualified HERMIT.Primitive.New as New
import qualified HERMIT.Primitive.Unfold as Unfold
import qualified HERMIT.Primitive.Unsafe as Unsafe

import HERMIT.PrettyPrinter.Common
import qualified HERMIT.PrettyPrinter.AST as AST
import qualified HERMIT.PrettyPrinter.Clean as Clean
import qualified HERMIT.PrettyPrinter.GHC as GHCPP

--------------------------------------------------------------------------

-- | List of all 'External's provided by HERMIT.
externals :: [External]
externals =
       Alpha.externals
    ++ Composite.externals
    ++ Debug.externals
    ++ FixPoint.externals
    ++ Fold.externals
    ++ Function.externals
    ++ GHC.externals
    ++ Inline.externals
    ++ Kure.externals
    ++ Local.externals
    ++ Navigation.externals
    ++ New.externals
    ++ Unfold.externals
    ++ Unsafe.externals

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
                -- Runs every command matching the tag predicate with innermostR (fix point anybuR),
                -- Only fails if all of them fail the first time.
                , external "bash" (bashR externs) (bashHelp externs) .+ Eval .+ Deep .+ Loop
                , external "debug-bash" (bashDebugR True externs)
                    [ "verbose bash - most useful with set-auto-corelint True" ] .+ Eval .+ Deep .+ Loop
                ]

--------------------------------------------------------------------------

-- | The pretty-printing dictionaries.
pp_dictionary :: Map String (PrettyH CoreTC)
pp_dictionary = fromList
        [ ("clean",  Clean.ppCoreTC)
        , ("ast",    AST.ppCoreTC)
        , ("ghc",    GHCPP.ppCoreTC)
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

bashPredicate :: CmdTag
bashPredicate = Bash

bashR :: [External] -> RewriteH Core
bashR = bashDebugR False

bashDebugR :: Bool -> [External] -> RewriteH Core
bashDebugR debug exts =
    setFailMsg "bash failed: nothing to do." $
    GHC.occurAnalyseR >>> repeatR (innermostR ( orR [ (if debug
                                                         then rr >>> Debug.observeR (externName e)
                                                         else rr)
                                                    | (e,rr) <- matchingExternals bashPredicate exts ]
                                              ) >>> GHC.occurAnalyseR
                                  )
    -- Occurrence Analysis is special because it always succeeds.  It's also expensive (I think) so I don't want to perform it at each node during the innermost traversal.

    -- It's still possible for some meta-data to be out-of-date after bash, despite the case analysis.  For example, if the focal point is a case-alt rhs, this won't update the identifer info of variables bound in the alternative.

bashHelp :: [External] -> [String]
bashHelp exts =
    "Iteratively apply the following rewrites until nothing changes:"
    : [ externName e | (e,_ :: RewriteH Core) <- matchingExternals bashPredicate exts ]

--------------------------------------------------------------------------

