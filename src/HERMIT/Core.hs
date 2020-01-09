{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}

module HERMIT.Core
    ( -- * Generic Data Type
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
    , endoFunTypeM
    , splitTyConAppM
    , splitFunTypeM
    , endoFunExprTypeM
    , funExprArgResTypesM
    , funExprsWithInverseTypes
    , appCount
    , mapAlts
    , substCoreAlt
    , substCoreExpr
    , betaReduceAll
    , mkDataConApp

      -- * Crumbs
    , Crumb(..)
    , showCrumbs
    , leftSibling
    , rightSibling
    ) where

import Control.Monad ((>=>))

import Data.List (intercalate)

import GHC.Generics

import Language.KURE.Combinators.Monad
import Language.KURE.MonadCatch

import HERMIT.GHC hiding (freeVarsBind)
import HERMIT.Utilities
import Control.Monad

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
#if __GLASGOW_HASKELL__ > 710
typeSyntaxEq (ForAllTy b1 ty1) (ForAllTy b2 ty2)    = tyBinderSyntaxEq (Named b1) (Named b2) && typeSyntaxEq ty1 ty2
#else
typeSyntaxEq (FunTy t1 ty1)    (FunTy t2 ty2)       = typeSyntaxEq t1 t2 && typeSyntaxEq ty1 ty2
typeSyntaxEq (ForAllTy v1 ty1) (ForAllTy v2 ty2)    = v1 == v2 && typeSyntaxEq ty1 ty2
#endif
typeSyntaxEq (TyConApp c1 ts1) (TyConApp c2 ts2)    = c1 == c2 && all2 typeSyntaxEq ts1 ts2
typeSyntaxEq _                 _                    = False

#if __GLASGOW_HASKELL__ > 710
tyBinderSyntaxEq :: TyBinder -> TyBinder -> Bool
tyBinderSyntaxEq (Named (TvBndr v1 a1)) (Named (TvBndr v2 a2)) = v1 == v2 && a1 == a2
tyBinderSyntaxEq (Anon t1)     (Anon t2)     = typeSyntaxEq t1 t2
tyBinderSyntaxEq _             _             = False
#endif

-- | Syntactic Equality of 'Coercion's.
coercionSyntaxEq :: Coercion -> Coercion -> Bool
coercionSyntaxEq (Refl role1 ty1)        (Refl role2 ty2)        = role1 == role2 && typeSyntaxEq ty1 ty2
coercionSyntaxEq (TyConAppCo role1 tc1 cos1) (TyConAppCo role2 tc2 cos2) = role1 == role2 && tc1 == tc2 && all2 coercionSyntaxEq cos1 cos2
coercionSyntaxEq (AppCo co11 co12)       (AppCo co21 co22)       = coercionSyntaxEq co11 co21 && coercionSyntaxEq co12 co22
#if __GLASGOW_HASKELL__ > 710
coercionSyntaxEq (ForAllCo v1 c1k c1)    (ForAllCo v2 c2k c2)    = v1 == v2 && coercionSyntaxEq c1k c2k && coercionSyntaxEq c1 c2
#else
coercionSyntaxEq (ForAllCo v1 co1)       (ForAllCo v2 co2)       = v1 == v2 && coercionSyntaxEq co1 co2
#endif
coercionSyntaxEq (CoVarCo v1)            (CoVarCo v2)            = v1 == v2
coercionSyntaxEq (AxiomInstCo con1 ind1 cos1) (AxiomInstCo con2 ind2 cos2) = con1 == con2 && ind1 == ind2 && all2 coercionSyntaxEq cos1 cos2
coercionSyntaxEq (LRCo lr1 co1)          (LRCo lr2 co2)          = lr1 == lr2 && coercionSyntaxEq co1 co2
#if __GLASGOW_HASKELL__ > 710
coercionSyntaxEq (UnivCo p1 role1 ty11 ty12) (UnivCo p2 role2 ty21 ty22) = ucpSyntaxEq p1 p2 && role1 == role2 && typeSyntaxEq ty11 ty21 && typeSyntaxEq ty12 ty22
#else
coercionSyntaxEq (UnivCo fs1 role1 ty11 ty12) (UnivCo fs2 role2 ty21 ty22) = fs1 == fs2 && role1 == role2 && typeSyntaxEq ty11 ty21 && typeSyntaxEq ty12 ty22
#endif
coercionSyntaxEq (SubCo co1)             (SubCo co2)             = coercionSyntaxEq co1 co2
coercionSyntaxEq (SymCo co1)             (SymCo co2)             = coercionSyntaxEq co1 co2
coercionSyntaxEq (TransCo co11 co12)     (TransCo co21 co22)     = coercionSyntaxEq co11 co21 && coercionSyntaxEq co12 co22
coercionSyntaxEq (NthCo r1 n1 co1)       (NthCo r2 n2 co2)       = r1 == r2 && n1 == n2 && coercionSyntaxEq co1 co2
#if __GLASGOW_HASKELL__ > 710
coercionSyntaxEq (InstCo c11 c12)        (InstCo c21 c22)        = coercionSyntaxEq c11 c21 && coercionSyntaxEq c12 c22
#else
coercionSyntaxEq (InstCo co1 ty1)        (InstCo co2 ty2)        = coercionSyntaxEq co1 co2 && typeSyntaxEq ty1 ty2
#endif
coercionSyntaxEq _                       _                       = False

#if __GLASGOW_HASKELL__ > 710
ucpSyntaxEq :: UnivCoProvenance -> UnivCoProvenance -> Bool
ucpSyntaxEq UnsafeCoerceProv    UnsafeCoerceProv    = True
ucpSyntaxEq (PhantomProv c1)    (PhantomProv c2)    = coercionSyntaxEq c1 c2
ucpSyntaxEq (PluginProv s1)     (PluginProv s2)     = s1 == s2
ucpSyntaxEq (ProofIrrelProv c1) (ProofIrrelProv c2) = coercionSyntaxEq c1 c2
-- ucpSyntaxEq (HoleProv _)        _                   = error "ucpSyntaxEq: impossible HoleProv"
-- ucpSyntaxEq _                   (HoleProv _)        = error "ucpSyntaxEq: impossible HoleProv"
ucpSyntaxEq _                   _                   = False
#endif

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
#if __GLASGOW_HASKELL__ > 710
coercionAlphaEq c1 c2 = eqCoercionX env c1 c2
  where env = mkRnEnv2 (mkInScopeSet (tyCoVarsOfCo c1 `unionVarSet` tyCoVarsOfCo c2))
#else
coercionAlphaEq = coreEqCoercion
#endif

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
-- We do not use GHC's exprSomeFreeVars because it does not return the full set of free vars for a Var.
-- It only returns the Var itself, rather than extendVarSet (freeVarsVar v) v like it should.

-- | Find all free identifiers in an expression.
freeIdsExpr :: CoreExpr -> IdSet
freeIdsExpr = filterVarSet isId . freeVarsExpr

-- | Find all locally defined free variables in an expression.
localFreeVarsExpr :: CoreExpr -> VarSet
localFreeVarsExpr = filterVarSet isLocalVar . freeVarsExpr

-- | Find all locally defined free identifiers in an expression.
localFreeIdsExpr :: CoreExpr -> VarSet
localFreeIdsExpr = filterVarSet isLocalId . freeVarsExpr

-- | Find all free variables in an expression.
freeVarsExpr :: CoreExpr -> VarSet
freeVarsExpr (Var v) = extendVarSet (freeVarsVar v) v
freeVarsExpr (Lit {}) = emptyVarSet
freeVarsExpr (App e1 e2) = freeVarsExpr e1 `unionVarSet` freeVarsExpr e2
freeVarsExpr (Lam b e) = delVarSet (freeVarsExpr e) b
freeVarsExpr (Let b e) = HERMIT.Core.freeVarsBind b `unionVarSet` delVarSetList (freeVarsExpr e) (bindersOf b)
freeVarsExpr (Case s b ty alts) = let altFVs = delVarSet (unionVarSets $ map freeVarsAlt alts) b
                                  in unionVarSets [freeVarsExpr s, freeVarsType ty, altFVs]
freeVarsExpr (Cast e co) = freeVarsExpr e `unionVarSet` freeVarsCoercion co
freeVarsExpr (Tick t e) = freeVarsTick t `unionVarSet` freeVarsExpr e
freeVarsExpr (Type ty) = freeVarsType ty
freeVarsExpr (Coercion co) = freeVarsCoercion co

freeVarsTick :: Tickish Id -> VarSet
freeVarsTick (Breakpoint _ ids) = mkVarSet ids
freeVarsTick _ = emptyVarSet

-- | Find all free identifiers in a binding group, which excludes any variables bound in the group.
freeVarsBind :: CoreBind -> VarSet
freeVarsBind (NonRec v e) = freeVarsExpr e `unionVarSet` freeVarsVar v
freeVarsBind (Rec defs)   = let (bs,es) = unzip defs
                             in delVarSetList (unionVarSets (map freeVarsVar bs ++ map freeVarsExpr es)) bs

-- | Find all free variables on a binder. Equivalent to idFreeVars, but safe to call on type bindings.
freeVarsVar :: Var -> VarSet
#if __GLASGOW_HASKELL__ > 710
freeVarsVar v = varTypeTyCoVars v `unionVarSet` bndrRuleAndUnfoldingVars v
#else
freeVarsVar v = varTypeTyVars v `unionVarSet` bndrRuleAndUnfoldingVars v
#endif

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
                  ProgCons bnd p -> HERMIT.Core.freeVarsBind bnd `unionVarSet` delVarSetList (freeVarsProg p) (bindVars bnd)

-- | Find all free variables in a type.
freeVarsType :: Type -> TyVarSet
#if __GLASGOW_HASKELL__ > 710
freeVarsType = tyCoVarsOfType
#else
freeVarsType = tyVarsOfType
#endif

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

-- | Get the quantified variables, domain, and codomain of a function type.
splitFunTypeM :: MonadCatch m => Type -> m ([TyVar], Type, Type)
splitFunTypeM ty = prefixFailMsg "Split function type failed: " $ do
    let (tvs, fTy) = splitForAllTys ty
    (argTy, resTy) <- maybeM "not a function type." $ splitFunTy_maybe fTy
    return (tvs, argTy, resTy)

-- | Return the domain/codomain type of an endofunction type.
endoFunTypeM :: MonadCatch m => Type -> m ([TyVar], Type)
endoFunTypeM ty =
  do (tvs,ty1,ty2) <- splitFunTypeM ty
     guardMsg (eqType ty1 ty2) ("argument and result types differ.")
     return (tvs, ty1)

-- | Return the domain/codomain type of an endofunction expression.
endoFunExprTypeM :: MonadCatch m => CoreExpr -> m ([TyVar], Type)
endoFunExprTypeM = exprTypeM >=> endoFunTypeM

-- | Return the domain and codomain types of a function expression.
funExprArgResTypesM :: MonadCatch m => CoreExpr -> m ([TyVar],Type,Type)
funExprArgResTypesM = exprTypeM >=> splitFunTypeM

-- | Check two expressions have types @a -> b@ and @b -> a@, returning @(a,b)@.
funExprsWithInverseTypes :: MonadCatch m => CoreExpr -> CoreExpr -> m (Type,Type)
funExprsWithInverseTypes f g =
  do (_,fdom,fcod) <- funExprArgResTypesM f -- TODO: don't throw away TyVars
     (_,gdom,gcod) <- funExprArgResTypesM g
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
#if __GLASGOW_HASKELL__ > 710
           | CastTy_Ty | CastTy_Co
           | CoercionTy_Co
#endif
           -- Coercion
           | Refl_Type
           | TyConAppCo_TyCon | TyConAppCo_Arg Int
           | AppCo_Fun | AppCo_Arg
           | ForAllCo_TyVar
#if __GLASGOW_HASKELL__ > 710
           | ForAllCo_KindCo | ForAllCo_Co
#else
           | ForAllCo_Body
#endif
           | CoVarCo_CoVar
           | AxiomInstCo_Axiom | AxiomInstCo_Index | AxiomInstCo_Arg Int
           | UnsafeCo_Left | UnsafeCo_Right
           | SymCo_Co
           | SubCo_Co
           | FunCo_Role | FunCo_Co_Left | FunCo_Co_Right

           | TransCo_Left | TransCo_Right
           | NthCo_Role | NthCo_Int | NthCo_Co
#if __GLASGOW_HASKELL__ > 710
           | InstCo_Left | InstCo_Right
#else
           | InstCo_Co | InstCo_Type
#endif
           | LRCo_LR | LRCo_Co
           | UnivCo_Dom | UnivCo_Ran
           -- Quantified
           | Forall_Body
           | Conj_Lhs | Conj_Rhs
           | Disj_Lhs | Disj_Rhs
           | Impl_Lhs | Impl_Rhs
           | Eq_Lhs | Eq_Rhs
           deriving (Eq, Generic, Read, Show)

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
#if __GLASGOW_HASKELL__ > 710
               CastTy_Ty      -> "castTy-ty"
               CastTy_Co      -> "castTy-co"
               CoercionTy_Co  -> "coercionTy-co"
#endif
               -- Coercions
               Refl_Type         -> "refl-type"
               TyConAppCo_Arg n  -> "coCon-arg " ++ show n
               AppCo_Fun         -> "appCo-fun"
               AppCo_Arg         -> "appCo-arg"
#if __GLASGOW_HASKELL__ > 710
               ForAllCo_KindCo   -> "coForall-kindco"
               ForAllCo_Co       -> "coForall-co"
#else
               ForAllCo_Body     -> "coForall-body"
#endif
               AxiomInstCo_Arg n -> "axiom-inst " ++ show n
               UnsafeCo_Left     -> "unsafe-left"
               UnsafeCo_Right    -> "unsafe-right"
               SymCo_Co          -> "sym-co"
               SubCo_Co          -> "sub-co"
               TransCo_Left      -> "trans-left"
               TransCo_Right     -> "trans-right"
               NthCo_Co          -> "nth-co"
#if __GLASGOW_HASKELL__ > 710
               InstCo_Left       -> "inst-left"
               InstCo_Right      -> "inst-right"
#else
               InstCo_Co         -> "inst-co"
               InstCo_Type       -> "inst-type"
#endif
               LRCo_Co           -> "lr-co"
               UnivCo_Dom        -> "univ-dom"
               UnivCo_Ran        -> "univ-ran"
               -- Quantified
               Forall_Body -> "forall-body"
               Conj_Lhs    -> "conj-lhs"
               Conj_Rhs    -> "conj-rhs"
               Disj_Lhs    -> "disj-lhs"
               Disj_Rhs    -> "disj-rhs"
               Impl_Lhs    -> "antecedent"
               Impl_Rhs    -> "consequent"
               Eq_Lhs      -> "eq-lhs"
               Eq_Rhs      -> "eq-rhs"
               _ -> "Warning: Crumb should not be in use!  This is probably Neil's fault."

-- | Converts a 'Crumb' into the 'Crumb' pointing to its left-sibling, if a such a 'Crumb' exists.
--   This is used for moving 'left' in the shell.
leftSibling :: Crumb -> Maybe Crumb
leftSibling = \case
                   ProgCons_Tail       -> Just ProgCons_Head
                   Rec_Def n | n > 0   -> Just (Rec_Def (n-1))
                   App_Arg             -> Just App_Fun
                   Let_Body            -> Just Let_Bind
                   Case_Alt n | n == 0 -> Just Case_Scrutinee
                              | n >  0 -> Just (Case_Alt (n-1))
                   _                   -> Nothing

-- | Converts a 'Crumb' into the 'Crumb' pointing to its right-sibling, if a such a 'Crumb' exists.
--   This is used for moving 'right' in the shell.
rightSibling :: Crumb -> Maybe Crumb
rightSibling = \case
                   ProgCons_Head       -> Just ProgCons_Tail
                   Rec_Def n           -> Just (Rec_Def (n+1))
                   App_Fun             -> Just App_Arg
                   Let_Bind            -> Just Let_Body
                   Case_Scrutinee      -> Just (Case_Alt 0)
                   Case_Alt n          -> Just (Case_Alt (n+1))
                   _                   -> Nothing

-----------------------------------------------------------------------

-- | Substitute all occurrences of a variable with an expression, in an expression.
substCoreExpr :: Var -> CoreExpr -> (CoreExpr -> CoreExpr)
substCoreExpr v e expr = substExpr (text "substCoreExpr") (extendSubst emptySub v e) expr
    where emptySub = mkEmptySubst (mkInScopeSet (localFreeVarsExpr (Let (NonRec v e) expr)))

-- | Substitute all occurrences of a variable with an expression, in a case alternative.
substCoreAlt :: Var -> CoreExpr -> CoreAlt -> CoreAlt
substCoreAlt v e alt = let (con, vs, rhs) = alt
                           inS            = (flip delVarSet v . unionVarSet (localFreeVarsExpr e) . localFreeVarsAlt) alt
                           subst          = extendSubst (mkEmptySubst (mkInScopeSet inS)) v e
                           (subst', vs')  = substBndrs subst vs
                        in (con, vs', substExpr (text "alt-rhs") subst' rhs)

-- | Beta-reduce as many lambda-binders as possible.
betaReduceAll :: CoreExpr -> [CoreExpr] -> (CoreExpr, [CoreExpr])
betaReduceAll (Lam v body) (a:as) = betaReduceAll (substCoreExpr v a body) as
betaReduceAll e            as     = (e,as)

-- | Build a constructor application.
--   Accepts a list of types to which the type constructor is instantiated. Ex.
--
-- > data T a b = C a b Int
--
-- Pseudocode:
--
-- > mkDataConApp [a',b'] C [x,y,z] ==> C a' b' (x::a') (y::b') (z::Int) :: T a' b'
--
mkDataConApp :: [Type] -> DataCon -> [Var] -> CoreExpr
mkDataConApp tys dc vs = mkCoreConApps dc (map Type tys ++ map (varToCoreExpr . zapVarOccInfo) vs)
