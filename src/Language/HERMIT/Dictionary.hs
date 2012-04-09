{-# LANGUAGE ExistentialQuantification #-}
-- The main namespace. Things tend to be untyped, because the API is accessed via (untyped) names.

module Language.HERMIT.Dictionary where

import GhcPlugins
import qualified Data.Map as Map
import Data.Map(Map)
import Data.Char
import qualified Language.Haskell.TH as TH

import Language.HERMIT.Types
import Language.HERMIT.KURE
import qualified Language.HERMIT.Expr as Expr
import Language.HERMIT.Command

import qualified Language.HERMIT.Primitive.Inline as Inline
import qualified Language.HERMIT.Primitive.Consider as Consider

all_rewrites :: Map String (Rewrite Core)
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


------------------------------------------------------------------------------------
-- The union of all possible results from a "well-typed" commands, from this dictionary.

interpExpr :: Expr.Expr -> Either String Command
interpExpr expr =
        case interpExpr' expr of
          Left msg -> Left msg
          Right (Left _) -> Left $ "interpExpr: bad type of expression"
          Right (Right cmd) -> Right $ cmd

data PartialCommand
        = RE_RR_RR   (Rewrite Core -> Rewrite Core)
        | RE_N_L     (TH.Name -> Lens Core Core)
        | RE_N       TH.Name

interpExpr' :: Expr.Expr -> Either String (Either PartialCommand Command)
interpExpr' (Expr.Lit str)
        = Right $ Left $ RE_N (TH.mkName str)
interpExpr' (Expr.Var ".")
        = Right $ Right $ PopFocus
interpExpr' (Expr.Var "pop")
        = Right $ Right $ PopFocus
interpExpr' (Expr.Var "reset")
        = Right $ Right $ ResetFocus
interpExpr' (Expr.Var str)
        | all isDigit str
        = Right $ Right $ PushFocus $ oneL (read str)
interpExpr' (Expr.Var str)
        | Just rr <- Map.lookup str all_rewrites
        = Right $ Right $ Apply rr
        | Just rr <- Map.lookup str selects
        = Right $ Left $ RE_N_L rr
        | Just rr <- Map.lookup str ho_rewrites
        = Right $ Left $ RE_RR_RR rr
        | otherwise
        = Left $ "can not find : " ++ show str
interpExpr' (Expr.App e1 e2) = do
        r1 <- interpExpr' e1
        r2 <- interpExpr' e2
        case (r1,r2) of
          (Left (RE_RR_RR ff), Right (Apply rr)) -> return $ Right $ Apply $ ff rr
          (Left (RE_N_L ff),   Left  (RE_N nm))  -> return $ Right $ PushFocus $ ff nm
          _ -> Left "type error in expression"

{-
          RE_RR rr -> Left $ "type error: a rewrite has been applied to an argument"
          RE_RR_RR ff -> do
                  a2 <- interpExpr' e2
                  case a2 of
                    RE_RR rr -> return $ RE_RR (ff rr)
                    _ -> Left $ "type error: lhs not a RR"
          RE_N_RR ff -> do
                  a2 <- interpExpr' e2
                  case a2 of
                    RE_N rr -> return $ RE_RR (ff rr)
                    _ -> Left $ "type error: lhs not a N"
          RE_N_RR_RR ff -> do
                  a2 <- interpExpr' e2
                  case a2 of
                    RE_N rr -> return $ RE_RR_RR (ff rr)
                    _ -> Left $ "type error: lhs not a N"
          RE_N nm -> Left $ "type error: names can not be used as functions"
-}

--------------------------------------------------------------



