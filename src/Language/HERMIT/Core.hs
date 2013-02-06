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
          , exprTypeOrKind
          , appCount
          , endoFunType
          , funArgResTypes
          , funsWithInverseTypes
) where

import GhcPlugins

import Language.KURE.Combinators.Monad
import Language.KURE.MonadCatch

---------------------------------------------------------------------

-- $typenote
--   NOTE: 'Type' is not included in the sum type.
--   However, we could have included it and provided the facility for descending into types.
--   We have not done so because
--     (a) we do not need that functionality, and
--     (b) the types are complicated and we're not sure that we understand them.

-- | Core is the sum type of all nodes in the AST that we wish to be able to traverse.
data Core = GutsCore  ModGuts            -- ^ The module.
          | ProgCore  CoreProg           -- ^ A program (a telescope of top-level binding groups).
          | BindCore  CoreBind           -- ^ A binding group.
          | DefCore   CoreDef            -- ^ A recursive definition.
          | ExprCore  CoreExpr           -- ^ An expression.
          | AltCore   CoreAlt            -- ^ A case alternative.

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

-- | GHC's 'exprType' function throws an error if applied to a 'Type' (but, inconsistently, return a 'Kind' if applied to a type variable).
--   This function returns the 'Kind' of a 'Type', but otherwise behaves as 'exprType'.
exprTypeOrKind :: CoreExpr -> Type
exprTypeOrKind (Type t) = typeKind t
exprTypeOrKind e        = exprType e

-----------------------------------------------------------------------

-- | Count the number of nested applications.
appCount :: CoreExpr -> Int
appCount (App e1 _) = appCount e1 + 1
appCount _          = 0

-----------------------------------------------------------------------

-- | Return the domain/codomain type of an endofunction expression.
endoFunType :: Monad m => CoreExpr -> m Type
endoFunType f = do (ty1,ty2) <- funArgResTypes f
                   guardMsg (eqType ty1 ty2) ("argument and result types differ.")
                   return ty1

-- | Return the domain and codomain types of a function expression.
funArgResTypes :: Monad m => CoreExpr -> m (Type,Type)
funArgResTypes e = maybe (fail "not a function type.") return (splitFunTy_maybe $ exprType e)

-- | Check two expressions have types @a -> b@ and @b -> a@, returning @(a,b)@.
funsWithInverseTypes :: MonadCatch m => CoreExpr -> CoreExpr -> m (Type,Type)
funsWithInverseTypes f g = do (fdom,fcod) <- funArgResTypes f
                              (gdom,gcod) <- funArgResTypes g
                              setFailMsg "functions do not have inverse types." $
                                do guardM (eqType fdom gcod)
                                   guardM (eqType gdom fcod)
                                   return (fdom,fcod)

-----------------------------------------------------------------------
