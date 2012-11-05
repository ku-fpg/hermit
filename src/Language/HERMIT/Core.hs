module Language.HERMIT.Core
          (
            -- * Generic Data Type
            -- $typenote
            Core(..)
          , CoreProg(..)
          , CoreDef(..)
          , CoreTickish
            -- * Conversions to/from 'Core'
          , defsToRecBind
          , defToIdExpr
          , progToBinds
          , bindsToProg
          , bindToIdExprs
            -- * Utilities
          , isType
          , typeExprToType
          , appCount
) where

import Data.Maybe(isJust)

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
          | ProgCore     CoreProg           -- ^ A program (a telescope of top-level binding groups).
          | BindCore     CoreBind           -- ^ A binding group.
          | DefCore      CoreDef            -- ^ A recursive definition.
          | ExprCore     CoreExpr           -- ^ An expression.
          | AltCore      CoreAlt            -- ^ A case alternative.

---------------------------------------------------------------------

-- | A program is a telescope of nested binding groups.
--   That is, each binding scopes over the remainder of the program.
--   In GHC Core, programs are encoded as ['CoreBind'].
--   This data type is isomorphic.
data CoreProg = ProgNil                     -- ^ An empty program.
              | ProgCons CoreBind CoreProg  -- ^ A binding group and the program it scopes over.

infixr 5 `ProgCons`

-- | Get the list of bindings in a program.
progToBinds :: CoreProg -> [CoreBind]
progToBinds ProgNil         = []
progToBinds (ProgCons bd p) = bd : progToBinds p

-- | Build a program from a list of bindings.
--   Note that bindings earlier in the list are considered scope over bindings later in the list.
bindsToProg :: [CoreBind] -> CoreProg
bindsToProg = foldr ProgCons ProgNil

-- | Extract the list of identifier/expression pairs from a binding group.
bindToIdExprs :: CoreBind -> [(Id,CoreExpr)]
bindToIdExprs (NonRec v e) = [(v,e)]
bindToIdExprs (Rec bds)    = bds

-- | A (potentially recursive) definition is an identifier and an expression.
--   In GHC Core, recursive definitions are encoded as ('Id', 'CoreExpr') pairs.
--   This data type is isomorphic.
data CoreDef = Def Id CoreExpr

-- | Convert a definition to an identifier/expression pair.
defToIdExpr :: CoreDef -> (Id,CoreExpr)
defToIdExpr (Def v e) = (v,e)

-- | Convert a list of recursive definitions into an (isomorphic) recursive binding group.
defsToRecBind :: [CoreDef] -> CoreBind
defsToRecBind = Rec . map defToIdExpr

-----------------------------------------------------------------------

-- | Unlike everything else, there is no synonym for 'Tickish' 'Id' provided by GHC, so we define one.
type CoreTickish = Tickish Id

-----------------------------------------------------------------------

-- | Succeeds if the expression is either a 'Type' or type 'Var'.
isType :: CoreExpr -> Bool
isType = isJust . typeExprToType

-- | Convert a 'CoreExpr' expression that \is\ a 'Type' into a 'Type'.
typeExprToType :: CoreExpr -> Maybe Type
typeExprToType (Type t)            = Just t
typeExprToType (Var v) | isTKVar v = Just (mkTyVarTy v)
typeExprToType _                   = Nothing

-----------------------------------------------------------------------

-- | Count the number of nested applications.
appCount :: CoreExpr -> Int
appCount (App e1 _) = appCount e1 + 1
appCount _          = 0

-----------------------------------------------------------------------
