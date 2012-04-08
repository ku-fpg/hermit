module Language.HERMIT.Primitive where

import GhcPlugins
import qualified Data.Map as Map
import Data.Map(Map)

import Language.HERMIT.Types

import qualified Language.HERMIT.Primitive.Inline as Inline

all_prims :: Map String (Rewrite Core)
all_prims = Map.unions
        [ fmap promoteR expr_prims
        ]

-- To consider:
--   should we include small programs, like unroll, as named arguments here?
--   In this case, these are not primitives, but named rewrites.

expr_prims :: Map String (Rewrite CoreExpr)
expr_prims = Map.fromList
        [ ("inline", Inline.inline)
--        , ("eta-expand",...)
--        , ("eta-reduction",...)
--        , ("beta-reduction",...)
--        , ("case-of-known-constructor", ...)
        ]
