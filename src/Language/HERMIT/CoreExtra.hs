module Language.HERMIT.CoreExtra
          (
            -- * GHC Core Extras
            CoreTickish
          , CoreDef(..)
          , defToRecBind
) where

import GhcPlugins

-----------------------------------------------------------------------

-- | Unlike everything else, there is no synonym for 'Tickish' 'Id' provided by GHC, so we provide one.
type CoreTickish = Tickish Id

-- | A (potentially recursive) definition is an identifier and an expression.
--   In GHC Core, recursive definitions are encoded as (Id, CoreExpr) pairs.
--   This data type is isomorphic.
data CoreDef = Def Id CoreExpr

-- | Convert a list of recursive definitions into an (isomorphic) recursive binding group.
defToRecBind :: [CoreDef] -> CoreBind
defToRecBind = Rec . map (\ (Def v e) -> (v,e))

-----------------------------------------------------------------------
