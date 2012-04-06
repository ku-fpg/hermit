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

expr_rewrites :: Map String (Rewrite CoreExpr)
expr_rewrites = Map.fromList
        [ ("inline",            Inline.inline)
--        , ("eta-expand",...)
--        , ("eta-reduction",...)
--        , ("beta-reduction",...)
--        , ("case-of-known-constructor", ...)
        ]

ho_rewrites :: Map String (Rewrite Blob -> Rewrite Blob)
ho_rewrites = Map.fromList
        [ ("bottomup",          bottomupR)
        , ("topdown",           topdownR)
        , ("try",               tryR)
        ]

selects :: Map String (TH.Name -> Rewrite Blob -> Rewrite Blob)
selects = Map.fromList
        [ ("consider",          considerK)
--        , ("inside",            insideK)
        ]

considerK :: TH.Name -> Rewrite Blob -> Rewrite Blob
considerK = undefined

------------------------------------------------------------------------------------

parseRewrite :: String -> Either String (Rewrite Blob)
parseRewrite str = do
        expr <- parser str
        re   <- interpHExpr expr
        case re of
           RE_RR rr -> return rr
           _ -> Left $ "parsed, interp, returned non RR"

{-
parseRewriteRewrite  :: String -> Either String (Rewrite Blob -> Rewrite Blob)
parseRewriteRewrite  str = do
        expr <- parser str
        re   <- interpHExpr expr
        case re of
           RE_RR rr -> return rr
           _ -> Left $ "parsed, interp, returned non RR"
-}
------------------------------------------------------------------------------------


data RewriteElem
        = RE_RR      (Rewrite Blob)
        | RE_RR_RR   (Rewrite Blob -> Rewrite Blob)
        | RE_N_RR    (TH.Name -> Rewrite Blob)
        | RE_N_RR_RR (TH.Name -> (Rewrite Blob -> Rewrite Blob))
        | RE_N       TH.Name

-- Very hacky (for now)
interpHExpr :: HExpr -> Either String RewriteElem
interpHExpr (HLit str)
        = Right $ RE_N (TH.mkName str)
interpHExpr (HVar str)
        | Just rr <- Map.lookup str all_rewrites
        = Right $ RE_RR rr
        | Just rr <- Map.lookup str ho_rewrites
        = Right $ RE_RR_RR rr
        | Just rr <- Map.lookup str selects
        = Right $ RE_N_RR_RR rr
        | otherwise
        = Left $ "can not find : " ++ show str
interpHExpr (HApp e1 e2) = do
        r <- interpHExpr e1
        case r of
          RE_RR rr -> Left $ "type error: a rewrite has been applied to an argument"
          RE_RR_RR ff -> do
                  a2 <- interpHExpr e2
                  case a2 of
                    RE_RR rr -> return $ RE_RR (ff rr)
                    _ -> Left $ "type error: lhs not a RR"
          RE_N_RR ff -> do
                  a2 <- interpHExpr e2
                  case a2 of
                    RE_N rr -> return $ RE_RR (ff rr)
                    _ -> Left $ "type error: lhs not a N"
          RE_N_RR_RR ff -> do
                  a2 <- interpHExpr e2
                  case a2 of
                    RE_N rr -> return $ RE_RR_RR (ff rr)
                    _ -> Left $ "type error: lhs not a N"
          RE_N nm -> Left $ "type error: names can not be used as functions"

--------------------------------------------------------------

data HExpr = HVar String
           | HLit String
           | HApp HExpr HExpr
        deriving Show

-- Cheap and cheerful parser
parser :: String -> Either String HExpr
parser str =
        case parseExpr str of
          ((e,""):_) -> return e
          _ -> Left $ "bad parse for: " ++ str

parseExpr0 :: ReadS HExpr
parseExpr0 = \ inp ->
        [ (HVar str,inp1)
        | (str,inp1) <- parseToken inp
        , all isAlpha str
        ] ++
        [ (HLit str,inp2)
        | ("#",inp1) <- parseToken inp
        , (str,inp2) <- parseToken inp1
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



