module Language.HERMIT.Primitive where

import GhcPlugins
import qualified Data.Map as Map
import Data.Map(Map)

import Language.HERMIT.Types

import qualified Language.HERMIT.Primitive.Inline as Inline

all_prims :: Map String (Rewrite Blob)
all_prims = Map.unions
        [ fmap promoteR expr_prims
        ]

expr_prims :: Map String (Rewrite CoreExpr)
expr_prims = Map.fromList
        [ ("inline", Inline.inline)
        ]
