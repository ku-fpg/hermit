module Language.HERMIT.CoreExtra
          (
            -- * Generic Data Type
            -- $typenote
            Core(..)
          , CoreDef(..)
            -- * GHC Core Extras
          , CoreTickish
          , defToRecBind
) where

import GhcPlugins

---------------------------------------------------------------------

-- $typenote
--   NOTE: 'Type' is not included in the generic datatype.
--   However, we could have included it and provided the facility for descending into types.
--   We have not done so because
--     (a) we do not need that functionality, and
--     (b) the types are complicated and we're not sure that we understand them.

-- | Core is the sum type of all nodes in the AST that we wish to be able to traverse.
--   All 'Node' instances in HERMIT define their 'Generic' type to be 'Core'.
data Core = ModGutsCore  ModGuts            -- ^ The module.
          | ProgramCore  CoreProgram        -- ^ A program (list of top-level bindings).
          | BindCore     CoreBind           -- ^ A binding group.
          | DefCore      CoreDef            -- ^ A recursive definition.
          | ExprCore     CoreExpr           -- ^ An expression.
          | AltCore      CoreAlt            -- ^ A case alternative.

---------------------------------------------------------------------

-- | A (potentially recursive) definition is an identifier and an expression.
--   In GHC Core, recursive definitions are encoded as ('Id', 'CoreExpr') pairs.
--   This data type is isomorphic.
data CoreDef = Def Id CoreExpr

-----------------------------------------------------------------------

-- | Unlike everything else, there is no synonym for 'Tickish' 'Id' provided by GHC, so we provide one.
type CoreTickish = Tickish Id

-- | Convert a list of recursive definitions into an (isomorphic) recursive binding group.
defToRecBind :: [CoreDef] -> CoreBind
defToRecBind = Rec . map (\ (Def v e) -> (v,e))

-----------------------------------------------------------------------
