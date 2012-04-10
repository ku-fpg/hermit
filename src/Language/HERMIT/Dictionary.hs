{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable, TypeFamilies, RankNTypes, GADTs #-}
-- The main namespace. Things tend to be untyped, because the API is accessed via (untyped) names.

module Language.HERMIT.Dictionary where

import GhcPlugins
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Char
import Data.Typeable
import Data.Dynamic
import qualified Language.Haskell.TH as TH

import Language.HERMIT.Types
import Language.HERMIT.KURE
import qualified Language.HERMIT.Expr as Expr
import Language.HERMIT.Command

import qualified Language.HERMIT.Primitive.Inline as Inline
import qualified Language.HERMIT.Primitive.Consider as Consider

commands :: Map String Command
commands = Map.fromList
        [ (".",                 PopFocus)
        , ("pop",               PopFocus)
        , ("reset",             ResetFocus)
        ]

rewrites :: Map String (Rewrite Core)
rewrites = Map.fromList
        [ ("inline",            promoteR Inline.inline)
--        , ("eta-expand",...)
--        , ("eta-reduction",...)
--        , ("beta-reduction",...)
--        , ("case-of-known-constructor", ...)
        ]

ho_rewrites :: Map String (Rewrite Core -> Rewrite Core)
ho_rewrites = Map.fromList
        [ ("bottomup",          bottomupR)
        , ("topdown",           topdownR)
        , ("try",               tryR)
        ]

selects :: Map String (TH.Name -> Lens Core Core)
selects = Map.fromList
        [ ("consider",          \ nm -> Consider.consider nm `glueL` promoteL)
--        , ("inside",            insideK)
--      select-case                             -- select the next case down
--      select-let                              -- select the next let down??
        ]


dictionary :: Map String Dynamic
dictionary = Map.unions
        [ fmap (toDyn . CommandBox)                                             commands
        , fmap (toDyn . RewriteCoreBox)                                         rewrites
        , fmap (toDyn . (\ f (RewriteCoreBox r) -> RewriteCoreBox (f r)))       ho_rewrites
        , fmap (toDyn . (\ f (NameBox r) -> LensCoreCoreBox (f r)))             selects
        ]

------------------------------------------------------------------------------------
-- The union of all possible results from a "well-typed" commands, from this dictionary.

interpExpr :: Expr.Expr -> Either String Command
interpExpr expr =
        case interpExpr' expr of
          Left msg -> Left msg
          Right dyn -> runInterp dyn
             [ Interp $ \ (CommandBox cmd)       -> Right $ cmd
             , Interp $ \ (RewriteCoreBox rr)    -> Right $ Apply rr
             , Interp $ \ (LensCoreCoreBox lens) -> Right $ PushFocus lens
             ]
             (Left $ "interpExpr: bad type of expression")

data Interp :: * -> * where
   Interp :: (Typeable a) => (a -> b) -> Interp b

runInterp :: Dynamic -> [Interp b] -> b -> b
runInterp dyn []                bad = bad
runInterp dyn (Interp f : rest) bad = case fromDynamic dyn of
   Just v -> f v
   Nothing -> runInterp dyn rest bad

--------------------------------------------------------------------------
-- Using boxes round things stop us needing deriving Dynamic everywhere.

data NameBox = NameBox TH.Name
        deriving (Typeable)

data RewriteCoreBox = RewriteCoreBox (Rewrite Core)
        deriving (Typeable)

data LensCoreCoreBox = LensCoreCoreBox (Lens Core Core)
        deriving (Typeable)

data CommandBox = CommandBox Command
        deriving (Typeable)

--------------------------------------------------------------------------

interpExpr' :: Expr.Expr -> Either String Dynamic -- (Either PartialCommand Command)
interpExpr' (Expr.Lit str)
        = Right $ toDyn $ NameBox $ TH.mkName str
interpExpr' (Expr.Var str)
        | all isDigit str
        = Right $ toDyn $ LensCoreCoreBox $ oneL (read str)
interpExpr' (Expr.Var str)
        | Just dyn <- Map.lookup str dictionary
        = Right $ dyn
        | otherwise
        = Left $ "can not find : " ++ show str
interpExpr' (Expr.App e1 e2) = do
        r1 <- interpExpr' e1
        r2 <- interpExpr' e2
        case dynApply r1 r2 of
           Nothing -> Left "apply failed"
           Just res -> return res

--------------------------------------------------------------



