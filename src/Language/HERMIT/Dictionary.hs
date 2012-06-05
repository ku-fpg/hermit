{-# LANGUAGE KindSignatures, GADTs #-}
-- The main namespace. Things tend to be untyped, because the API is accessed via (untyped) names.

module Language.HERMIT.Dictionary where

import Prelude hiding (lookup)

import Data.Default (def)
import Data.Dynamic
import Data.List
import qualified Data.Map as M
import Data.Maybe

import GhcPlugins

import Language.HERMIT.HermitKure
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
import qualified Language.HERMIT.PrettyPrinter.GHC as GHCPP

--------------------------------------------------------------------------

prim_externals :: [External]
prim_externals =    Kure.externals
                 ++ Consider.externals
                 ++ Inline.externals
                 ++ Subst.externals
                 ++ Local.externals
                 ++ New.externals

-- The GHC.externals here is a bit of a hack. Not sure about this
all_externals :: [External] -> ModGuts -> [External]
all_externals my_externals guts = prim_externals ++ my_externals ++ GHC.externals guts

-- create the dictionary
dictionary :: [External] -> M.Map String [Dynamic]
dictionary externs = toDictionary externs'
  where
        externs' = externs ++
                [ external "help"            (help externs Nothing Nothing)
                    [ "lists all commands" ]
                , external "help" (help externs Nothing . Just :: String -> String)
                    [ "help with a specific cmd or path"
                    , "use 'help ls' to see a list of paths"
                    , "use 'help \"let\"' to see cmds whose names contain \"let\"" ]
                , external "help" ((\c p -> help externs (Just c) (Just p)) :: String -> String -> String)
                    [ "help ls <path> to list commands in a specific path" ]
{- todo: finish, by modifying Interp.hs
                , external "help" ((\p -> intercalate ", " $ map externName $ filter (tagMatch p) externs) :: TagE -> String)
                    [ "show rewrites matched by a tag predicate" ]
-}
                , bashExternal externs
                ]

--------------------------------------------------------------------------
-- The pretty printing dictionaries
pp_dictionary :: M.Map String (PrettyOptions -> PrettyH Core)
pp_dictionary = M.fromList
        [ ("clean",  Clean.corePrettyH)
        , ("ast",    AST.corePrettyH)
        , ("ghc",    GHCPP.corePrettyH)
        ]

-- each pretty printer can suggest some options
pp_opt_dictionary :: M.Map String PrettyOptions
pp_opt_dictionary = M.fromList
        [ ("clean", def)
        , ("ast",  def)
        , ("ghc",  def)
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
help _ _ _ = error "bad help arguments"

--------------------------------------------------------------------------

-- TODO: supply map of command-name -> arguments?
-- otherwise fromDynamic will fail for any rewrite that takes arguments.
metaCmd :: (Tag a)
        => String                             -- ^ name of the command
        -> [External]                         -- ^ universe of commands to search
        -> a                                  -- ^ tag matching predicate
        -> ([RewriteH Core] -> RewriteH Core) -- ^ means to combine the matched rewrites
        -> [String]                           -- ^ help text preamble
        -> External
metaCmd name externs p combine hlp = external name (combine rws) (hlp ++ concat helps)
    where (rws, helps) = unzip [ (rw, externName e : externHelp e)
                               | e <- externs
                               , tagMatch p e
                               , Just rw <- [fmap unbox $ fromDynamic $ externFun e] ]

-- Runs every command tagged with 'Bash' with innermostR (fix point anybuR),
-- if any of them succeed, then it tries all of them again.
-- Only fails if all of them fail the first time.
bashExternal :: [External] -> External
bashExternal es = metaCmd "bash" es (Local .& Eval .& (notT Unimplemented)) (innermostR . orR)
                          [ "Iteratively apply the following rewrites until nothing changes." ]

bash :: [External] -> RewriteH Core
bash = unbox . fromJust . fromDynamic . externFun . bashExternal
