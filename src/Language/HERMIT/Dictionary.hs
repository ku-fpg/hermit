{-# LANGUAGE ExistentialQuantification #-}
-- The main namespace. Things tend to be untyped, because the API is accessed via (untyped) names.

module Language.HERMIT.Dictionary where

import GhcPlugins
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Char

import Language.HERMIT.Types
import Language.HERMIT.KURE

import qualified Language.Haskell.TH as TH

import qualified Language.HERMIT.Primitive.Inline as Inline

all_rewrites :: Map String (Rewrite Blob)
all_rewrites = Map.unions
        [ fmap promoteR expr_rewrites
        ]

ho_rewrites :: Map String (Rewrite Blob -> Rewrite Blob)
ho_rewrites = Map.fromList
        [ ("bottomup",          bottomupR)
        , ("topdown",           topdownR)
        , ("try",               tryR)
        ]


expr_rewrites :: Map String (Rewrite CoreExpr)
expr_rewrites = Map.fromList
        [ ("inline",            Inline.inline)
--        , ("eta-expand",...)
--        , ("eta-reduction",...)
--        , ("beta-reduction",...)
--        , ("case-of-known-constructor", ...)
        ]


selects :: Map String (TH.Name -> Rewrite Blob -> Rewrite Blob)
selects = Map.fromList
        [ ("consider",          considerK)
        ]


considerK :: TH.Name -> Rewrite Blob -> Rewrite Blob
considerK = undefined

-- Cheap and cherful parser
parser :: String -> Either String (Rewrite Blob)
parser str =
        case parseExpr str of
          [] -> Left $ "bad parse for: " ++ str
          ((e,""):_) -> interpHExpr e

-- Very hacky (for now)
interpHExpr :: HExpr -> Either String (Rewrite Blob)
interpHExpr (HVar str) =
        case Map.lookup str all_rewrites of
          Just rr -> Right $ rr
          Nothing -> Left $ "can not find : " ++ show str
interpHExpr (HApp e1 e2) = do
        r <- interpHExprHO e1
        case r of
          RRRR f -> do
                  a2 <- interpHExpr e2
                  return (f a2)

data HOR
        = RRRR (Rewrite Blob -> Rewrite Blob)


interpHExprHO :: HExpr -> Either String HOR
interpHExprHO (HVar str) =
        case Map.lookup str ho_rewrites of
          Just rr -> Right $ RRRR rr
          Nothing -> Left $ "can not find : " ++ show str
{-
interpHExprHO (HApp e1 e2) = do
        HOR k rr <- interpHExprHO e1
        a2 <- k e2
        return (HOR (rr a2)
-}
interpHExprHO _ = Left $ "bad higher-orderness"

data HType = HRR        -- R a
           | HRR2RR     -- R a -> R a

data HExpr = HVar String
           | HApp HExpr HExpr
        deriving Show

parseExpr0 :: ReadS HExpr
parseExpr0 = \ inp ->
        [ (HVar str,inp1)
        | (str,inp1) <- parseToken inp
        , all isAlpha str
        ] ++
        [ (e,inp3)
        | ("(",inp1) <- parseToken inp
        , (e,inp2) <- parseExpr inp1
        , (")",inp3) <- parseToken inp2
        ]
parseExpr :: ReadS HExpr
parseExpr = \ inp ->
        [ (foldl HApp e es,inp2)
        | (e,inp1) <- parseExpr0 inp
        , (es,inp2) <- parseExprs inp1
        ]

parseExprs :: ReadS [HExpr]
parseExprs = \ inp ->
        [ (e:es,inp2)
        | (e,inp1) <- parseExpr0 inp
        , (es,inp2) <- parseExprs inp1
        ] ++
        [ ([], inp) ]

item :: String -> ReadS ()
item str = \ inp ->
        [ ((),rest)
        | (tok,rest) <- parseToken inp
        , tok == str
        ]

parseToken :: ReadS String
parseToken = \ inp -> if null inp then [] else lex inp



