{-# LANGUAGE CPP, LambdaCase #-}
module HERMIT.Core
          (
          -- * Generic Data Type
            CoreProg(..)
          , CoreDef(..)
          , CoreTickish
          -- * Equality
          -- | We define both syntactic equality and alpha equality.

          -- ** Syntactic Equality
          , progSyntaxEq
          , bindSyntaxEq
          , defSyntaxEq
          , exprSyntaxEq
          , altSyntaxEq
          , typeSyntaxEq
          , coercionSyntaxEq

          -- ** Alpha Equality
          , progAlphaEq
          , bindAlphaEq
          , defAlphaEq
          , exprAlphaEq
          , altAlphaEq
          , typeAlphaEq
          , coercionAlphaEq

          -- * Conversions to/from 'Core'
          , defsToRecBind
          , defToIdExpr
          , progToBinds
          , bindsToProg
          , bindToVarExprs

          -- * Collecting variable bindings
          , progIds
          , bindVars
          , defId
          , altVars

          -- * Collecting free variables
          -- $freeVarsNote
          , freeVarsProg
          , freeVarsBind
          , freeVarsDef
          , freeVarsExpr
          , freeVarsAlt
          , freeVarsVar
          , localFreeVarsAlt
          , freeVarsType
          , freeVarsCoercion
          , localFreeVarsExpr
          , freeIdsExpr
          , localFreeIdsExpr

          -- * Utilities
          , isCoArg
          , exprKindOrType
          , exprTypeM
          , endoFunType
          , splitTyConAppM
          , splitFunTypeM
          , endoFunExprType
          , funExprArgResTypes
          , funExprsWithInverseTypes
          , appCount
          , mapAlts

          -- * Crumbs
          , Crumb(..)
          , showCrumbs
--          , crumbToDeprecatedInt
          , deprecatedLeftSibling
          , deprecatedRightSibling
) where

import Control.Monad ((>=>))

import Language.KURE.Combinators.Monad
import Language.KURE.MonadCatch

import HERMIT.GHC
import HERMIT.Utilities

import Data.List (intercalate)

-----------------------------------------------------------------------

-- | Unlike everything else, there is no synonym for 'Tickish' 'Id' provided by GHC, so we define one.
type CoreTickish = Tickish Id

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

-- | Extract the list of variable/expression pairs from a binding group.
bindToVarExprs :: CoreBind -> [(Var,CoreExpr)]
bindToVarExprs (NonRec v e) = [(v,e)]
bindToVarExprs (Rec bds)    = bds
{-# INLINE bindToVarExprs #-}

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

-- Syntactic Equality

-- | Syntactic Equality of programs.
progSyntaxEq :: CoreProg -> CoreProg -> Bool
progSyntaxEq ProgNil ProgNil                       = True
progSyntaxEq (ProgCons bnd1 p1) (ProgCons bnd2 p2) = bindSyntaxEq bnd1 bnd2 && progSyntaxEq p1 p2
progSyntaxEq _ _                                   = False

-- | Syntactic Equality of binding groups.
bindSyntaxEq :: CoreBind -> CoreBind -> Bool
bindSyntaxEq (NonRec v1 e1) (NonRec v2 e2) = v1 == v2 && exprSyntaxEq e1 e2
bindSyntaxEq (Rec ies1)     (Rec ies2)     = all2 (\ (i1,e1) (i2,e2) -> i1 == i2 && exprSyntaxEq e1 e2) ies1 ies2
bindSyntaxEq _              _              = False

-- | Syntactic Equality of recursive definitions.
defSyntaxEq :: CoreDef -> CoreDef -> Bool
defSyntaxEq (Def i1 e1) (Def i2 e2) = i1 == i2 && exprSyntaxEq e1 e2

-- | Syntactic Equality of expressions.
exprSyntaxEq :: CoreExpr -> CoreExpr -> Bool
exprSyntaxEq (Var i1)             (Var i2)             = i1 == i2
exprSyntaxEq (Lit l1)             (Lit l2)             = l1 == l2
exprSyntaxEq (App f1 e1)          (App f2 e2)          = exprSyntaxEq f1 f2 && exprSyntaxEq e1 e2
exprSyntaxEq (Lam v1 e1)          (Lam v2 e2)          = v1 == v2 && exprSyntaxEq e1 e2
exprSyntaxEq (Let b1 e1)          (Let b2 e2)          = bindSyntaxEq b1 b2 && exprSyntaxEq e1 e2
exprSyntaxEq (Case s1 w1 ty1 as1) (Case s2 w2 ty2 as2) = w1 == w2 && exprSyntaxEq s1 s2 && all2 altSyntaxEq as1 as2 && typeSyntaxEq ty1 ty2
exprSyntaxEq (Cast e1 co1)        (Cast e2 co2)        = exprSyntaxEq e1 e2 && coercionSyntaxEq co1 co2
exprSyntaxEq (Tick t1 e1)         (Tick t2 e2)         = t1 == t2 && exprSyntaxEq e1 e2
exprSyntaxEq (Type ty1)           (Type ty2)           = typeSyntaxEq ty1 ty2
exprSyntaxEq (Coercion co1)       (Coercion co2)       = coercionSyntaxEq co1 co2
exprSyntaxEq _                    _                    = False

-- | Syntactic Equality of case alternatives.
altSyntaxEq :: CoreAlt -> CoreAlt -> Bool
altSyntaxEq (c1,vs1,e1) (c2,vs2,e2) = c1 == c2 && vs1 == vs2 && exprSyntaxEq e1 e2

-- | Syntactic Equality of 'Type's.
typeSyntaxEq :: Type -> Type -> Bool
typeSyntaxEq (TyVarTy v1)      (TyVarTy v2)         = v1 == v2
typeSyntaxEq (LitTy l1)        (LitTy l2)           = l1 == l2
typeSyntaxEq (AppTy t1 ty1)    (AppTy t2 ty2)       = typeSyntaxEq t1 t2 && typeSyntaxEq ty1 ty2
typeSyntaxEq (FunTy t1 ty1)    (FunTy t2 ty2)       = typeSyntaxEq t1 t2 && typeSyntaxEq ty1 ty2
typeSyntaxEq (ForAllTy v1 ty1) (ForAllTy v2 ty2)    = v1 == v2 && typeSyntaxEq ty1 ty2
typeSyntaxEq (TyConApp c1 ts1) (TyConApp c2 ts2)    = c1 == c2 && all2 typeSyntaxEq ts1 ts2
typeSyntaxEq _                 _                    = False

-- | Syntactic Equality of 'Coercion's.
coercionSyntaxEq :: Coercion -> Coercion -> Bool
#if __GLASGOW_HASKELL__ > 706
coercionSyntaxEq (Refl role1 ty1)        (Refl role2 ty2)        = role1 == role2 && typeSyntaxEq ty1 ty2
coercionSyntaxEq (TyConAppCo role1 tc1 cos1) (TyConAppCo role2 tc2 cos2) = role1 == role2 && tc1 == tc2 && all2 coercionSyntaxEq cos1 cos2
#else
coercionSyntaxEq (Refl ty1)              (Refl ty2)              = typeSyntaxEq ty1 ty2
coercionSyntaxEq (TyConAppCo tc1 cos1)   (TyConAppCo tc2 cos2)   = tc1 == tc2 && all2 coercionSyntaxEq cos1 cos2
#endif
coercionSyntaxEq (AppCo co11 co12)       (AppCo co21 co22)       = coercionSyntaxEq co11 co21 && coercionSyntaxEq co12 co22
coercionSyntaxEq (ForAllCo v1 co1)       (ForAllCo v2 co2)       = v1 == v2 && coercionSyntaxEq co1 co2
coercionSyntaxEq (CoVarCo v1)            (CoVarCo v2)            = v1 == v2
#if __GLASGOW_HASKELL__ > 706
coercionSyntaxEq (AxiomInstCo con1 ind1 cos1) (AxiomInstCo con2 ind2 cos2) = con1 == con2 && ind1 == ind2 && all2 coercionSyntaxEq cos1 cos2
coercionSyntaxEq (LRCo lr1 co1)          (LRCo lr2 co2)          = lr1 == lr2 && coercionSyntaxEq co1 co2
coercionSyntaxEq (UnivCo role1 ty11 ty12) (UnivCo role2 ty21 ty22) = role1 == role2 && typeSyntaxEq ty11 ty21 && typeSyntaxEq ty12 ty22
#else
coercionSyntaxEq (AxiomInstCo con1 cos1) (AxiomInstCo con2 cos2) = con1 == con2 && all2 coercionSyntaxEq cos1 cos2
coercionSyntaxEq (UnsafeCo ty11 ty12)    (UnsafeCo ty21 ty22)    = typeSyntaxEq ty11 ty21 && typeSyntaxEq ty12 ty22
#endif
coercionSyntaxEq (SymCo co1)             (SymCo co2)             = coercionSyntaxEq co1 co2
coercionSyntaxEq (TransCo co11 co12)     (TransCo co21 co22)     = coercionSyntaxEq co11 co21 && coercionSyntaxEq co12 co22
coercionSyntaxEq (NthCo n1 co1)          (NthCo n2 co2)          = n1 == n2 && coercionSyntaxEq co1 co2
coercionSyntaxEq (InstCo co1 ty1)        (InstCo co2 ty2)        = coercionSyntaxEq co1 co2 && typeSyntaxEq ty1 ty2
coercionSyntaxEq _                       _                       = False

-----------------------------------------------------------------------

-- Alpha Equality

-- | Alpha equality of programs.
progAlphaEq :: CoreProg -> CoreProg -> Bool
progAlphaEq ProgNil ProgNil                       = True
progAlphaEq (ProgCons bnd1 p1) (ProgCons bnd2 p2) = bindVars bnd1 == bindVars bnd2 && bindAlphaEq bnd1 bnd2 && progAlphaEq p1 p2
progAlphaEq _ _                                   = False

-- The ideas for this function are directly extracted from
-- the GHC function, CoreUtils.eqExprX
-- | Alpha equality of binding groups.
bindAlphaEq :: CoreBind -> CoreBind -> Bool
bindAlphaEq (NonRec _ e1) (NonRec _ e2) = exprAlphaEq e1 e2
bindAlphaEq (Rec ps1)     (Rec ps2)     = all2 (eqExprX id_unf env) rs1 rs2
  where
    id_unf _   = noUnfolding      -- Don't expand
    (bs1,rs1)  = unzip ps1
    (bs2,rs2)  = unzip ps2
    inScopeSet = mkInScopeSet $ exprsFreeVars (rs1 ++ rs2)
    env        = rnBndrs2 (mkRnEnv2 inScopeSet) bs1 bs2
bindAlphaEq _ _ = False

-- | Alpha equality of recursive definitions.
defAlphaEq :: CoreDef -> CoreDef -> Bool
defAlphaEq d1 d2 = defsToRecBind [d1] `bindAlphaEq` defsToRecBind [d2]

-- | Alpha equality of expressions.
exprAlphaEq :: CoreExpr -> CoreExpr -> Bool
exprAlphaEq e1 e2 = eqExpr (mkInScopeSet $ exprsFreeVars [e1, e2]) e1 e2

-- The ideas for this function are directly extracted from
-- the GHC function, CoreUtils.eqExprX
-- | Alpha equality of case alternatives.
altAlphaEq :: CoreAlt -> CoreAlt -> Bool
altAlphaEq (c1,vs1,e1) (c2,vs2,e2) = c1 == c2 && eqExprX id_unf env e1 e2
  where
    id_unf _    = noUnfolding      -- Don't expand
    inScopeSet  = mkInScopeSet $ exprsFreeVars [e1,e2]
    env         = rnBndrs2 (mkRnEnv2 inScopeSet) vs1 vs2

-- | Alpha equality of types.
typeAlphaEq :: Type -> Type -> Bool
typeAlphaEq = eqType

-- | Alpha equality of coercions.
coercionAlphaEq :: Coercion -> Coercion -> Bool
coercionAlphaEq = coreEqCoercion

-----------------------------------------------------------------------

-- | List all identifiers bound at the top-level in a program.
progIds :: CoreProg -> [Id]
progIds = \case
             ProgNil        -> []
             ProgCons bnd p -> bindVars bnd ++ progIds p

-- | List all variables bound in a binding group.
bindVars :: CoreBind -> [Var]
bindVars = \case
              NonRec v _ -> [v]
              Rec ds     -> map fst ds

-- | Return the identifier bound by a recursive definition.
defId :: CoreDef -> Id
defId (Def i _) = i

-- | List the variables bound by a case alternative.
altVars :: CoreAlt -> [Var]
altVars (_,vs,_) = vs

-----------------------------------------------------------------------

-- $freeVarsNote
-- The GHC Function exprFreeVars defined in "CoreFVs" only returns *locally-defined* free variables.
-- In HERMIT, this is typically not what we want, so we define our own functions.
-- We reuse some of the functionality in "CoreFVs", but alas much of it is not exposed, so we have to reimplement some of it.

-- | Find all free variables in an expression.
freeVarsExpr :: CoreExpr -> VarSet
freeVarsExpr = exprSomeFreeVars (const True)

-- | Find all free identifiers in an expression.
freeIdsExpr :: CoreExpr -> IdSet
freeIdsExpr = exprSomeFreeVars isId

-- | Find all locally defined free variables in an expression.
localFreeVarsExpr :: CoreExpr -> VarSet
localFreeVarsExpr = exprSomeFreeVars isLocalVar

-- | Find all locally defined free identifiers in an expression.
localFreeIdsExpr :: CoreExpr -> VarSet
localFreeIdsExpr = exprSomeFreeVars isLocalId


-- | Find all free identifiers in a binding group, which excludes any variables bound in the group.
freeVarsBind :: CoreBind -> VarSet
freeVarsBind (NonRec v e) = freeVarsExpr e `unionVarSet` freeVarsVar v
freeVarsBind (Rec defs)   = let (bs,es) = unzip defs
                             in delVarSetList (unionVarSets (map freeVarsVar bs ++ map freeVarsExpr es)) bs

-- | Find all free variables on a binder. Equivalent to idFreeVars, but safe to call on type bindings.
freeVarsVar :: Var -> VarSet
freeVarsVar v = varTypeTyVars v `unionVarSet` bndrRuleAndUnfoldingVars v

-- | Find all free variables in a recursive definition, which excludes the bound variable.
freeVarsDef :: CoreDef -> VarSet
freeVarsDef (Def v e) = delVarSet (freeVarsExpr e) v `unionVarSet` freeVarsVar v

-- | Find all free variables in a case alternative, which excludes any variables bound in the alternative.
freeVarsAlt :: CoreAlt -> VarSet
freeVarsAlt (_,bs,e) = delVarSetList (freeVarsExpr e `unionVarSet` unionVarSets (map freeVarsVar bs)) bs

-- | Find all free local variables in a case alternative, which excludes any variables bound in the alternative.
localFreeVarsAlt :: CoreAlt -> VarSet
localFreeVarsAlt (_,bs,e) = delVarSetList (localFreeVarsExpr e `unionVarSet` unionVarSets (map freeVarsVar bs)) bs

-- | Find all free variables in a program.
freeVarsProg :: CoreProg -> VarSet
freeVarsProg = \case
                  ProgNil        -> emptyVarSet
                  ProgCons bnd p -> freeVarsBind bnd `unionVarSet` delVarSetList (freeVarsProg p) (bindVars bnd)

-- | Find all free variables in a type.
freeVarsType :: Type -> TyVarSet
freeVarsType = tyVarsOfType

-- | Find all free variables in a coercion.
freeVarsCoercion :: Coercion -> VarSet
freeVarsCoercion = tyCoVarsOfCo

-----------------------------------------------------------------------

-- | GHC's 'exprType' function throws an error if applied to a 'Type'.
--   This function returns the 'Kind' of a 'Type', but otherwise behaves as 'exprType'.
exprKindOrType :: CoreExpr -> KindOrType
exprKindOrType (Type t)  = typeKind t
exprKindOrType e         = exprType e

-- | GHC's 'exprType' function throws an error if applied to a 'Type'.
--   This function catches that case as failure in an arbitrary monad.
exprTypeM :: Monad m => CoreExpr -> m Type
exprTypeM (Type _) = fail "exprTypeM failed: expression is a type, so does not have a type."
exprTypeM e        = return (exprType e)

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

-- | Map a function over the RHS of each case alternative.
mapAlts :: (CoreExpr -> CoreExpr) -> [CoreAlt] -> [CoreAlt]
mapAlts f alts = [ (ac, vs, f e) | (ac, vs, e) <- alts ]

-----------------------------------------------------------------------

-- | As 'splitTyConApp', catching failure in a monad.
splitTyConAppM :: Monad m => Type -> m (TyCon, [Type])
splitTyConAppM = maybeM "splitTyConApp failed." . splitTyConApp_maybe

-- | Return the domain and codomain types of a function type, if it is a function type.
splitFunTypeM :: Monad m => Type -> m (Type,Type)
splitFunTypeM = maybeM "not a function type." . splitFunTy_maybe

-- | Return the domain/codomain type of an endofunction type.
endoFunType :: Monad m => Type -> m Type
endoFunType ty =
  do (ty1,ty2) <- splitFunTypeM ty
     guardMsg (eqType ty1 ty2) ("argument and result types differ.")
     return ty1

-- | Return the domain/codomain type of an endofunction expression.
endoFunExprType :: Monad m => CoreExpr -> m Type
endoFunExprType = exprTypeM >=> endoFunType

-- | Return the domain and codomain types of a function expression.
funExprArgResTypes :: Monad m => CoreExpr -> m (Type,Type)
funExprArgResTypes = exprTypeM >=> splitFunTypeM

-- | Check two expressions have types @a -> b@ and @b -> a@, returning @(a,b)@.
funExprsWithInverseTypes :: MonadCatch m => CoreExpr -> CoreExpr -> m (Type,Type)
funExprsWithInverseTypes f g =
  do (fdom,fcod) <- funExprArgResTypes f
     (gdom,gcod) <- funExprArgResTypes g
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

-- Note, these should match the external names in HERMIT.Primitive.Navigation.Crumbs
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
