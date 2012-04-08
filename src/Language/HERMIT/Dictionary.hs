{-# LANGUAGE ExistentialQuantification #-}
-- The main namespace. Things tend to be untyped, because the API is accessed via (untyped) names.

module Language.HERMIT.Dictionary where

import GhcPlugins
import qualified Data.Map as Map
import Data.Map(Map)

import Language.HERMIT.Types
import Language.HERMIT.KURE
import Language.HERMIT.Command

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
--      select-case                             -- select the next case down
--      select-let                              -- select the next let down??
        ]

considerK :: TH.Name -> Rewrite Blob -> Rewrite Blob
considerK = undefined

------------------------------------------------------------------------------------
-- The union of all possible results from a "well-typed" commands, from this dictionary.

data TypedCommand
        = RE_RR      (Rewrite Blob)
        | RE_RR_RR   (Rewrite Blob -> Rewrite Blob)
        | RE_N_RR_RR (TH.Name -> (Rewrite Blob -> Rewrite Blob))
        | RE_N_RR    (TH.Name -> Rewrite Blob)
        | RE_N       TH.Name
        | RE_B       BaseCommand

data BaseCommand
        = POP
        | TOP           -- pop until at the top of the tree

-- Very hacky (for now)
interpCommand :: Command -> Either String TypedCommand
interpCommand (HLit str)
        = Right $ RE_N (TH.mkName str)
interpCommand (HVar str)
        | Just rr <- Map.lookup str all_rewrites
        = Right $ RE_RR rr
        | Just rr <- Map.lookup str ho_rewrites
        = Right $ RE_RR_RR rr
        | Just rr <- Map.lookup str selects
        = Right $ RE_N_RR_RR rr
        | otherwise
        = Left $ "can not find : " ++ show str
interpCommand (HApp e1 e2) = do
        r <- interpCommand e1
        case r of
          RE_RR rr -> Left $ "type error: a rewrite has been applied to an argument"
          RE_RR_RR ff -> do
                  a2 <- interpCommand e2
                  case a2 of
                    RE_RR rr -> return $ RE_RR (ff rr)
                    _ -> Left $ "type error: lhs not a RR"
          RE_N_RR ff -> do
                  a2 <- interpCommand e2
                  case a2 of
                    RE_N rr -> return $ RE_RR (ff rr)
                    _ -> Left $ "type error: lhs not a N"
          RE_N_RR_RR ff -> do
                  a2 <- interpCommand e2
                  case a2 of
                    RE_N rr -> return $ RE_RR_RR (ff rr)
                    _ -> Left $ "type error: lhs not a N"
          RE_N nm -> Left $ "type error: names can not be used as functions"

--------------------------------------------------------------



