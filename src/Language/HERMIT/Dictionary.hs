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

import qualified Language.HERMIT.Primitive.Command as Command
import qualified Language.HERMIT.Primitive.Kure as Kure
import qualified Language.HERMIT.Primitive.Consider as Consider
import qualified Language.HERMIT.Primitive.Inline as Inline
import qualified Language.HERMIT.Primitive.Case as Case
import qualified Language.HERMIT.Primitive.Subst as Subst
import qualified Language.HERMIT.Primitive.Local as Local
import qualified Language.HERMIT.Primitive.New as New

import Language.HERMIT.PrettyPrinter
-- import qualified Language.HERMIT.PrettyPrinter.AST
--------------------------------------------------------------------------

prim_externals :: [External]
prim_externals =    Command.externals
                 ++ Kure.externals
                 ++ Consider.externals
                 ++ Inline.externals
                 ++ Case.externals
                 ++ Subst.externals
                 ++ Local.externals
                 ++ New.externals

all_externals :: [External]
all_externals =    prim_externals
                ++ [ external "bash" (promoteR bash) bashHelp .+ MetaCmd
                   , external "help"            (help all_externals Nothing Nothing)
                        [ "lists all commands" ]
                   , external "help" (help all_externals Nothing . Just :: String -> String)
                        [ "help with a specific cmd or path"
                        , "use 'help ls' to see a list of paths"
                        , "use 'help \"let\"' to see cmds whose names contain \"let\"" ]
                   , external "help" ((\c p -> help all_externals (Just c) (Just p)) :: String -> String -> String)
                        [ "help ls <path> to list commands in a specific path" ]
                   ]

dictionary :: M.Map String [Dynamic]
dictionary = toDictionary all_externals

--------------------------------------------------------------------------
-- The pretty printing dictionaries
pp_dictionary :: M.Map String (PrettyH Core)
pp_dictionary = M.fromList
        [ ("ghc",ghcCorePrettyH)
        ]

--------------------------------------------------------------------------

-- The union of all possible results from a "well-typed" commands, from this dictionary.

interpExprH :: ExprH -> Either String KernelCommand
interpExprH expr =
        case interpExpr expr of
          Left msg  -> Left msg
          Right dyn -> runInterp dyn
             [ Interp $ \ (KernelCommandBox cmd)      -> Right cmd
             , Interp $ \ (RewriteCoreBox rr)         -> Right $ Apply rr
             , Interp $ \ (TranslateCoreStringBox tt) -> Right $ Query tt
             , Interp $ \ (LensCoreCoreBox l)         -> Right $ PushFocus l
             , Interp $ \ (IntBox i)                  -> Right $ PushFocus $ childL i
             , Interp $ \ (StringBox str)             -> Left $ str
             ]
             (Left "interpExpr: bad type of expression")

data Interp :: * -> * where
   Interp :: Typeable a => (a -> b) -> Interp b

runInterp :: [Dynamic] -> [Interp b] -> b -> b
runInterp dyns interps bad = head $
             [f a
             | Interp f <- interps
             , Just a <- map fromDynamic dyns
             ] ++ [ bad ]


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

interpExpr :: ExprH -> Either String [Dynamic]
interpExpr = interpExpr' False

interpExpr' :: Bool -> ExprH -> Either String [Dynamic]
interpExpr' _   (SrcName str) = return [ toDyn $ NameBox $ TH.mkName str ]
interpExpr' rhs (CmdName str)
  | all isDigit str                     = return [ toDyn $ IntBox $ read str ]
  | Just dyn <- M.lookup str dictionary = if rhs
                                          then return (toDyn (StringBox str) : dyn)
                                          else return dyn
  -- not a command, try as a string arg... worst case: dynApply fails with "bad type of expression"
  -- best case: 'help ls' works instead of 'help "ls"'. this is likewise done in then clause above
  | rhs                                 = return [toDyn $ StringBox str]
  | otherwise                           = Left $ "Unrecognised command: " ++ show str
interpExpr' rhs (StrName str)           = if rhs
                                          then return [ toDyn $ StringBox str ]
                                          else return []
interpExpr' _ (AppH e1 e2)              = dynAppMsg (interpExpr' False e1) (interpExpr' True e2)

dynAppMsg :: Either String [Dynamic] -> Either String [Dynamic] -> Either String [Dynamic]
dynAppMsg f x = liftM2 dynApply' f x >>= return
   where
           dynApply' :: [Dynamic] -> [Dynamic] -> [Dynamic]
           dynApply' fs xs = [ r | f <- fs, x <- xs, Just r <- return (dynApply f x)]

--------------------------------------------------------------------------

-- Runs every command tagged with 'Bash' with innermostR (fix point anybuR),
-- if any of them succeed, then it tries all of them again.
-- Only fails if all of them fail the first time.
bash :: RewriteH (Generic CoreExpr)
bash = innermostR $ orR [ maybe (fail "bash: fromDynamic failed") (anybuR . unbox)
                          $ fromDynamic $ externFun $ cmd
                        | cmd <- all_externals, cmd `hasTag` Bash ]

bashHelp :: [String]
bashHelp = "Bash runs the following commands:"
           : (make_help $ filter (`hasTag` Bash) all_externals)
