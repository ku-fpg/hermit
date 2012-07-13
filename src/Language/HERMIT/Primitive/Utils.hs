
-- Utils for primitives, not the primitives themselves

module Language.HERMIT.Primitive.Utils where

import GhcPlugins as GHC

-- appCount counts the number of applications / arguments are present
appCount :: CoreExpr -> Int
appCount (App e1 _) = appCount e1 + 1
appCount _          = 0

