{-# LANGUAGE GADTs, ScopedTypeVariables #-}

module Language.HERMIT.Dictionary
       ( -- * The HERMIT Dictionary
         -- | This is the main namespace. Things tend to be untyped, because the API is accessed via (untyped) names.
         Dictionary
       , all_externals
       , dictionary
       , pp_dictionary
)  where

-- import Data.Default (def)
import Data.Dynamic
import Data.List
import Data.Map (Map, fromList, toList)

import Language.HERMIT.Core
import Language.HERMIT.Kure
import Language.HERMIT.External

import qualified Language.HERMIT.Primitive.Kure as Kure
import qualified Language.HERMIT.Primitive.Navigation as Navigation
import qualified Language.HERMIT.Primitive.Inline as Inline
import qualified Language.HERMIT.Primitive.Local as Local
import qualified Language.HERMIT.Primitive.New as New
import qualified Language.HERMIT.Primitive.Debug as Debug
import qualified Language.HERMIT.Primitive.GHC as GHC
import qualified Language.HERMIT.Primitive.FixPoint as FixPoint
import qualified Language.HERMIT.Primitive.Fold as Fold
import qualified Language.HERMIT.Primitive.Unfold as Unfold
import qualified Language.HERMIT.Primitive.AlphaConversion as Alpha


import Language.HERMIT.PrettyPrinter.Common
import qualified Language.HERMIT.PrettyPrinter.AST as AST
import qualified Language.HERMIT.PrettyPrinter.Clean as Clean
import qualified Language.HERMIT.PrettyPrinter.GHC as GHCPP

--------------------------------------------------------------------------

-- | A 'Dictionary' is a collection of 'Dynamic's.
--   Looking up a 'Dynamic' (via a 'String' key) returns a list, as there can be multiple 'Dynamic's with the same name.
type Dictionary = Map String [Dynamic]

prim_externals :: [External]
prim_externals
               =    Kure.externals
                 ++ Navigation.externals
                 ++ Inline.externals
                 ++ Local.externals
                 ++ Debug.externals
                 ++ New.externals
                 ++ FixPoint.externals
                 ++ Fold.externals
                 ++ Unfold.externals
                 ++ Alpha.externals

-- The GHC.externals here is a bit of a hack. Not sure about this
-- | Augment a list of 'External's by adding all of HERMIT's primitive 'External's, plus any GHC RULES pragmas in the module.
all_externals :: [External] -> [External]
all_externals my_externals = prim_externals ++ my_externals ++ GHC.externals

-- | Create a dictionary from a list of 'External's.
dictionary :: [External] -> Dictionary
dictionary externs = toDictionary externs'
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
                , let bashPredicate = Bash -- Shallow .& Eval .& (notT Loop)
                  in external "bash"
                              (metaCmd externs bashPredicate (setFailMsg "Nothing to do." . innermostR . orR))
                              (metaHelp externs bashPredicate
                                [ "Iteratively apply the following rewrites until nothing changes:" ])
                              .+ Eval .+ Deep .+ Loop
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
help_command externals m
        | [(ct :: CmdTag,"")] <- reads m
        = unlines $ make_help $ filter (tagMatch ct) externals
help_command externals "all"
        = unlines $ make_help externals
help_command _ "categories" = unlines $
                [ "categories" ] ++
                [ "----------" ] ++
                [ txt ++ " " ++ replicate (16 - length txt) '.' ++ " " ++ desc
                | (cmd,desc) <- dictionaryOfTags
                , let txt = show cmd
                ]

help_command externals m = unlines $ make_help $ pathPrefix m
    where pathPrefix p = filter (isInfixOf p . externName) externals

layoutTxt :: Int -> [String] -> [String]
layoutTxt n (w1:w2:ws) | length w1 + length w2 >= n = w1 : layoutTxt n (w2:ws)
                       | otherwise = layoutTxt n ((w1 ++ " " ++ w2) : ws)
layoutTxt _ other = other

--------------------------------------------------------------------------

-- TODO: We need to think harder about bash/metaCmd.

-- TODO: supply map of command-name -> arguments?
-- otherwise fromDynamic will fail for any rewrite that takes arguments.
metaCmd :: Tag a
        => [External]                         -- ^ universe of commands to search
        -> a                                  -- ^ tag matching predicate
        -> ([RewriteH Core] -> RewriteH Core) -- ^ means to combine the matched rewrites
        -> RewriteH Core
metaCmd externs p = ($ [ rw | e <- externs
                            , tagMatch p e
                            , Just rw <- [fmap unbox $ fromDynamic $ externFun e] ])

metaHelp :: Tag a
        => [External]                         -- ^ universe of commands to search
        -> a                                  -- ^ tag matching predicate
        -> [String]                           -- ^ help text preamble
        -> [String]
metaHelp externs p = (++ [ externName e
                         | e <- externs
                         , tagMatch p e
                         -- necessary so we don't list things that don't type correctly
                         , Just (_ :: RewriteH Core) <- [fmap unbox $ fromDynamic $ externFun e] ])

------------------------------------
