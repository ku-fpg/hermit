{-# LANGUAGE LambdaCase #-}

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
          , isCoArg
          , exprTypeOrKind
          , endoFunType
          , funArgResTypes
          , funsWithInverseTypes
          , appCount
            -- * Crumbs
          , Crumb(..)
--          , crumbToDeprecatedInt
          , deprecatedLeftSibling
          , deprecatedRightSibling
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
-- recursive, don't inline

-- | Build a program from a list of bindings.
--   Note that bindings earlier in the list are considered scope over bindings later in the list.
bindsToProg :: [CoreBind] -> CoreProg
bindsToProg = foldr ProgCons ProgNil
{-# INLINE bindsToProg #-}

-- | Extract the list of identifier/expression pairs from a binding group.
bindToIdExprs :: CoreBind -> [(Id,CoreExpr)]
bindToIdExprs (NonRec v e) = [(v,e)]
bindToIdExprs (Rec bds)    = bds
{-# INLINE bindToIdExprs #-}

-- | A (potentially recursive) definition is an identifier and an expression.
--   In GHC Core, recursive definitions are encoded as ('Id', 'CoreExpr') pairs.
--   This data type is isomorphic.
data CoreDef = Def Id CoreExpr

-- | Convert a definition to an identifier/expression pair.
defToIdExpr :: CoreDef -> (Id,CoreExpr)
defToIdExpr (Def v e) = (v,e)
{-# INLINE defToIdExpr #-}

-- | Convert a list of recursive definitions into an (isomorphic) recursive binding group.
defsToRecBind :: [CoreDef] -> CoreBind
defsToRecBind = Rec . map defToIdExpr
{-# INLINE defsToRecBind #-}

-----------------------------------------------------------------------

-- | Unlike everything else, there is no synonym for 'Tickish' 'Id' provided by GHC, so we define one.
type CoreTickish = Tickish Id

-----------------------------------------------------------------------

-- | GHC's 'exprType' function throws an error if applied to a 'Type' (but, inconsistently, return a 'Kind' if applied to a type variable).
--   This function returns the 'Kind' of a 'Type', but otherwise behaves as 'exprType'.
exprTypeOrKind :: CoreExpr -> Type
exprTypeOrKind (Type t) = typeKind t
exprTypeOrKind e        = exprType e
{-# INLINE exprTypeOrKind #-}

-- | Returns @True@ iff the expression is a 'Coercion' expression at its top level.
isCoArg :: CoreExpr -> Bool
isCoArg (Coercion {}) = True
isCoArg _             = False
{-# INLINE isCoArg #-}

-----------------------------------------------------------------------

-- | Count the number of nested applications.
appCount :: CoreExpr -> Int
appCount (App e1 _) = appCount e1 + 1
appCount _          = 0
{-# INLINE appCount #-}

-----------------------------------------------------------------------

-- | Return the domain/codomain type of an endofunction expression.
endoFunType :: Monad m => CoreExpr -> m Type
endoFunType f = do (ty1,ty2) <- funArgResTypes f
                   guardMsg (eqType ty1 ty2) ("argument and result types differ.")
                   return ty1
{-# INLINE endoFunType #-}

-- | Return the domain and codomain types of a function expression.
funArgResTypes :: Monad m => CoreExpr -> m (Type,Type)
funArgResTypes e = maybe (fail "not a function type.") return (splitFunTy_maybe $ exprType e)
{-# INLINE funArgResTypes #-}

-- | Check two expressions have types @a -> b@ and @b -> a@, returning @(a,b)@.
funsWithInverseTypes :: MonadCatch m => CoreExpr -> CoreExpr -> m (Type,Type)
funsWithInverseTypes f g = do (fdom,fcod) <- funArgResTypes f
                              (gdom,gcod) <- funArgResTypes g
                              setFailMsg "functions do not have inverse types." $
                                do guardM (eqType fdom gcod)
                                   guardM (eqType gdom fcod)
                                   return (fdom,fcod)
{-# INLINE funsWithInverseTypes #-}

-----------------------------------------------------------------------

-- | Crumbs record a path through the tree, using descriptive constructor names.
data Crumb = ModGuts_Prog
           | ProgCons_Bind | ProgCons_Tail
           | NonRec_RHS | NonRec_Var | Rec_Def Int
           | Def_Id | Def_RHS
           | Var_Id | Lit_Lit | App_Fun | App_Arg | Lam_Var | Lam_Body | Let_Bind | Let_Body | Case_Scrutinee | Case_Binder | Case_Type | Case_Alt Int | Cast_Expr | Cast_Co | Tick_Tick | Tick_Expr | Type_Type | Co_Co
           | Alt_Con | Alt_Var Int | Alt_RHS
           | TyVarTy_TyVar | LitTy_TyLit | AppTy_Fun | AppTy_Arg | TyConApp_TyCon | TyConApp_Arg Int | FunTy_Dom | FunTy_CoDom | ForAllTy_Var | ForAllTy_Body
           deriving (Eq,Show)
           -- TODO: Write a prettier Show instance
{-
-- | Earlier versions of HERMIT used 'Int' as the crumb type.
--   This function maps a 'Crumb' back to that corresponding 'Int', for backwards compatibility purposes.
crumbToDeprecatedInt :: Crumb -> Maybe Int
crumbToDeprecatedInt = \case
                          ModGuts_Prog   -> Just 0
                          ProgCons_Bind  -> Just 0
                          ProgCons_Tail  -> Just 1
                          NonRec_RHS     -> Just 0
                          NonRec_Var     -> Nothing
                          Rec_Def n      -> Just n
                          Def_Id         -> Nothing
                          Def_RHS        -> Just 0
                          App_Fun        -> Just 0
                          App_Arg        -> Just 1
                          Lam_Var        -> Nothing
                          Lam_Body       -> Just 0
                          Let_Bind       -> Just 0
                          Let_Body       -> Just 1
                          Case_Scrutinee -> Just 0
                          Case_Binder    -> Nothing
                          Case_Type      -> Nothing
                          Case_Alt n     -> Just (n + 1)
                          Cast_Expr      -> Just 0
                          Cast_Co        -> Nothing
                          Tick_Tick      -> Nothing
                          Tick_Expr      -> Just 0
                          Type_Type      -> Nothing
                          Co_Co          -> Nothing
                          Alt_Con        -> Nothing
                          Alt_Var _      -> Nothing
                          Alt_RHS        -> Just 0
-}
-- | Converts a 'Crumb' into the 'Crumb' pointing to its left-sibling, if a such a 'Crumb' exists.
--   This is for backwards compatibility purposes with the old Int representation.
deprecatedLeftSibling :: Crumb -> Maybe Crumb
deprecatedLeftSibling = \case
                           ProgCons_Tail       -> Just ProgCons_Bind
                           Rec_Def n | n > 0   -> Just (Rec_Def (n-1))
                           App_Arg             -> Just App_Fun
                           Let_Body            -> Just Let_Bind
                           Case_Alt n | n == 0 -> Just Case_Scrutinee
                                      | n >  0 -> Just (Case_Alt (n-1))
                           _                   -> Nothing

-- | Converts a 'Crumb' into the 'Crumb' pointing to its right-sibling, if a such a 'Crumb' exists.
--   This is for backwards compatibility purposes with the old Int representation.
deprecatedRightSibling :: Crumb -> Maybe Crumb
deprecatedRightSibling = \case
                           ProgCons_Bind       -> Just ProgCons_Tail
                           Rec_Def n           -> Just (Rec_Def (n+1))
                           App_Fun             -> Just App_Arg
                           Let_Bind            -> Just Let_Body
                           Case_Scrutinee      -> Just (Case_Alt 0)
                           Case_Alt n          -> Just (Case_Alt (n+1))
                           _                   -> Nothing


-----------------------------------------------------------------------
