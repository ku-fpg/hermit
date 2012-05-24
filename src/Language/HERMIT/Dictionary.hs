{-# LANGUAGE KindSignatures, GADTs #-}
-- The main namespace. Things tend to be untyped, because the API is accessed via (untyped) names.

module Language.HERMIT.Dictionary where

import Prelude hiding (lookup)

import Data.Char
import Data.Dynamic
import Data.List
import qualified Data.Map as M

import Control.Monad (liftM2)

import GhcPlugins

import qualified Language.Haskell.TH as TH

import Language.KURE

import Language.HERMIT.HermitExpr
import Language.HERMIT.HermitKure
import Language.HERMIT.Kernel
import Language.HERMIT.External

--import qualified Language.HERMIT.Primitive.Command as Command
import qualified Language.HERMIT.Primitive.Kure as Kure
import qualified Language.HERMIT.Primitive.Consider as Consider
import qualified Language.HERMIT.Primitive.Inline as Inline
import qualified Language.HERMIT.Primitive.Subst as Subst
import qualified Language.HERMIT.Primitive.Local as Local
import qualified Language.HERMIT.Primitive.New as New
import qualified Language.HERMIT.Primitive.GHC as GHC


import Language.HERMIT.PrettyPrinter
import qualified Language.HERMIT.PrettyPrinter.AST as AST
import qualified Language.HERMIT.PrettyPrinter.Clean as Clean

--------------------------------------------------------------------------

prim_externals :: [External]
prim_externals =    Kure.externals
                 ++ Consider.externals
                 ++ Inline.externals
                 ++ Subst.externals
                 ++ Local.externals
                 ++ New.externals
                 ++ GHC.externals

-- create the dictionary
dictionary :: [External] -> M.Map String [Dynamic]
dictionary my_externals = toDictionary all_externals
  where
        all_externals = prim_externals ++ my_externals ++
                [ external "bash" (promoteR (bash all_externals)) (bashHelp all_externals) .+ MetaCmd
                   , external "help"            (help all_externals Nothing Nothing)
                        [ "lists all commands" ]
                   , external "help" (help all_externals Nothing . Just :: String -> String)
                        [ "help with a specific cmd or path"
                        , "use 'help ls' to see a list of paths"
                        , "use 'help \"let\"' to see cmds whose names contain \"let\"" ]
                   , external "help" ((\c p -> help all_externals (Just c) (Just p)) :: String -> String -> String)
                        [ "help ls <path> to list commands in a specific path" ]
                   ]


--------------------------------------------------------------------------
-- The pretty printing dictionaries
pp_dictionary :: M.Map String (PrettyH Core)
pp_dictionary = M.fromList
        [ ("ghc",    ghcCorePrettyH)
        , ("clean",   Clean.corePrettyH)
        , ("ast",     AST.corePrettyH True)
        , ("astFull", AST.corePrettyH False)
        ]

--------------------------------------------------------------------------

make_help :: [External] -> [String]
make_help = concatMap snd . M.toList . toHelp

help :: [External] -> Maybe String -> Maybe String -> String
-- 'help ls' case
help externals Nothing (Just "ls") = help externals (Just "ls") Nothing
-- 'help' or 'help <search string>' case
help externals Nothing m = unlines $ make_help $ maybe externals pathPrefix m
    where pathPrefix p = filter (isInfixOf p . externName) externals
-- 'help ls <path>' case
help externals (Just "ls") m = unlines $ map toLine groups
    where fixHyphen p | last p == '-' = p
                      | otherwise     = p ++ "-"
          optParens s | null s = ""
                      | otherwise = "  (" ++ s ++ ")"
          prefix = maybe "" fixHyphen m
          groups = groupBy ((==) `on` fst)
                 $ sortBy (compare `on` fst)
                   [ (fst $ span (/='-') $ drop (length prefix) n, n)
                   | n <- map externName externals, prefix `isPrefixOf` n ]
          toLine [] = ""
          toLine ((d,cmd):r) = d ++ optParens (intercalate ", " [ cmd' | cmd' <- cmd : map snd r, cmd' /= d ])

--------------------------------------------------------------------------
-- Runs every command tagged with 'Bash' with innermostR (fix point anybuR),
-- if any of them succeed, then it tries all of them again.
-- Only fails if all of them fail the first time.
bash :: [External] -> RewriteH (Generic CoreExpr)
bash all_externals = innermostR $ orR [ maybe (fail "bash: fromDynamic failed") (anybuR . unbox)
                          $ fromDynamic $ externFun $ cmd
                        | cmd <- all_externals, cmd `hasTag` Bash ]

bashHelp :: [External] -> [String]
bashHelp all_externals = "Bash runs the following commands:"
           : (make_help $ filter (`hasTag` Bash) all_externals)
