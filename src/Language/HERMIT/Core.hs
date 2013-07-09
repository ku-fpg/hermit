{-# LANGUAGE LambdaCase #-}

module Language.HERMIT.Core
          (
            -- * Generic Data Type
            CoreProg(..)
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
          , showCrumbs
--          , crumbToDeprecatedInt
          , deprecatedLeftSibling
          , deprecatedRightSibling
) where

import GhcPlugins

import Language.KURE.Combinators.Monad
import Language.KURE.MonadCatch

import Data.List (intercalate)

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

-- | GHC's 'exprType' function throws an error if applied to a 'Type'.
--   This function returns the 'Kind' of a 'Type', but otherwise behaves as 'exprType'.
exprTypeOrKind :: CoreExpr -> KindOrType
exprTypeOrKind (Type t)  = typeKind t
exprTypeOrKind e         = exprType e

-- | Returns @True@ iff the expression is a 'Coercion' expression at its top level.
isCoArg :: CoreExpr -> Bool
isCoArg (Coercion {}) = True
isCoArg _             = False

-----------------------------------------------------------------------

-- | Count the number of nested applications.
appCount :: CoreExpr -> Int
appCount (App e1 _) = appCount e1 + 1
appCount _          = 0
-- don't inline, recursive

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

-- | Crumbs record a path through the tree, using descriptive constructor names.
data Crumb =
           -- ModGuts
             ModGuts_Prog
           -- Prog
           | ProgCons_Head | ProgCons_Tail
           -- Bind
           | NonRec_RHS | NonRec_Var
           | Rec_Def Int
           -- Def
           | Def_Id | Def_RHS
           -- Expr
           | Var_Id
           | Lit_Lit
           | App_Fun | App_Arg
           | Lam_Var | Lam_Body
           | Let_Bind | Let_Body
           | Case_Scrutinee | Case_Binder | Case_Type | Case_Alt Int
           | Cast_Expr | Cast_Co
           | Tick_Tick | Tick_Expr
           | Type_Type
           | Co_Co
           -- Alt
           | Alt_Con | Alt_Var Int | Alt_RHS
           -- Type
           | TyVarTy_TyVar
           | LitTy_TyLit
           | AppTy_Fun | AppTy_Arg
           | TyConApp_TyCon | TyConApp_Arg Int
           | FunTy_Dom | FunTy_CoDom
           | ForAllTy_Var | ForAllTy_Body
           -- Coercion
           | Refl_Type
           | TyConAppCo_TyCon | TyConAppCo_Arg Int
           | AppCo_Fun | AppCo_Arg
           | ForAllCo_TyVar | ForAllCo_Body
           | CoVarCo_CoVar
           | AxiomInstCo_Axiom | AxiomInstCo_Index | AxiomInstCo_Arg Int
           | UnsafeCo_Left | UnsafeCo_Right
           | SymCo_Co
           | TransCo_Left | TransCo_Right
           | NthCo_Int | NthCo_Co
           | InstCo_Co | InstCo_Type
           | LRCo_LR | LRCo_Co
           deriving (Eq,Read,Show)
           -- TODO: Write a prettier Show instance


showCrumbs :: [Crumb] -> String
showCrumbs crs = "[" ++ intercalate ", " (map showCrumb crs) ++ "]"

-- Note, these should match the external names in Language.HERMIT.Primitive.Navigation.Crumbs
showCrumb :: Crumb -> String
showCrumb = \case
               ModGuts_Prog   -> "prog"
               ProgCons_Head  -> "prog-head"
               ProgCons_Tail  -> "prog-tail"
               NonRec_RHS     -> "nonrec-rhs"
               Rec_Def n      -> "rec-def " ++ show n
               Def_RHS        -> "def-rhs"
               App_Fun        -> "app-fun"
               App_Arg        -> "app-arg"
               Lam_Body       -> "lam-body"
               Let_Bind       -> "let-bind"
               Let_Body       -> "let-body"
               Case_Scrutinee -> "case-expr"
               Case_Type      -> "case-type"
               Case_Alt n     -> "case-alt " ++ show n
               Cast_Expr      -> "cast-expr"
               Cast_Co        -> "cast-co"
               Tick_Expr      -> "tick-expr"
               Alt_RHS        -> "alt-rhs"
               Type_Type      -> "type"
               Co_Co          -> "coercion"
               -- Types
               AppTy_Fun      -> "appTy-fun"
               AppTy_Arg      -> "appTy-arg"
               TyConApp_Arg n -> "tyCon-arg " ++ show n
               FunTy_Dom      -> "fun-dom"
               FunTy_CoDom    -> "fun-cod"
               ForAllTy_Body  -> "forall-body"
               -- Coercions
               Refl_Type         -> "refl-type"
               TyConAppCo_Arg n  -> "coCon-arg " ++ show n
               AppCo_Fun         -> "appCo-fun"
               AppCo_Arg         -> "appCo-arg"
               ForAllCo_Body     -> "coForall-body"
               AxiomInstCo_Arg n -> "axiom-inst " ++ show n
               UnsafeCo_Left     -> "unsafe-left"
               UnsafeCo_Right    -> "unsafe-right"
               SymCo_Co          -> "sym-co"
               TransCo_Left      -> "trans-left"
               TransCo_Right     -> "trans-right"
               NthCo_Co          -> "nth-co"
               InstCo_Co         -> "inst-co"
               InstCo_Type       -> "inst-type"
               LRCo_Co           -> "lr-co"

               _              -> "Warning: Crumb should not be in use!  This is probably Neil's fault."

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
                           ProgCons_Tail       -> Just ProgCons_Head
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
                           ProgCons_Head       -> Just ProgCons_Tail
                           Rec_Def n           -> Just (Rec_Def (n+1))
                           App_Fun             -> Just App_Arg
                           Let_Bind            -> Just Let_Body
                           Case_Scrutinee      -> Just (Case_Alt 0)
                           Case_Alt n          -> Just (Case_Alt (n+1))
                           _                   -> Nothing


-----------------------------------------------------------------------
