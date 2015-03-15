{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}

module HERMIT.Kure.Universes
    ( -- * Universes
      Core(..)
    , TyCo(..)
    , CoreTC(..)
    , QC(..)
      -- * Equality
      -- ** Syntactic Equality
    , coreSyntaxEq
    , tyCoSyntaxEq
    , coreTCSyntaxEq
      -- ** Alpha Equality
    , coreAlphaEq
    , tyCoAlphaEq
    , coreTCAlphaEq
      -- ** Collecting Free Variables
    , freeVarsCore
    , freeVarsTyCo
    , freeVarsCoreTC
      -- * Promotion Combinators
      -- ** Transform Promotions
    , promoteModGutsT
    , promoteProgT
    , promoteBindT
    , promoteDefT
    , promoteExprT
    , promoteAltT
    , promoteTypeT
    , promoteCoercionT
    , promoteQuantifiedT
    , promoteClauseT
    , promoteCoreT
    , promoteCoreTCT
      -- ** Rewrite Promotions
    , promoteModGutsR
    , promoteProgR
    , promoteBindR
    , promoteDefR
    , promoteExprR
    , promoteAltR
    , promoteTypeR
    , promoteCoercionR
    , promoteQuantifiedR
    , promoteClauseR
    , promoteCoreR
    , promoteCoreTCR
      -- ** BiRewrite Promotions
    , promoteExprBiR
    ) where

import Language.KURE.Transform
import Language.KURE.Injection
import Language.KURE.BiTransform

import HERMIT.Core
import HERMIT.GHC
import HERMIT.Lemma

---------------------------------------------------------------------

-- | Core is a universe for use by KURE.  Core = ModGuts + CoreProg + CoreBind + CoreDef + CoreExpr + CoreAlt
data Core = GutsCore  ModGuts            -- ^ The module.
          | ProgCore  CoreProg           -- ^ A program (a telescope of top-level binding groups).
          | BindCore  CoreBind           -- ^ A binding group.
          | DefCore   CoreDef            -- ^ A recursive definition.
          | ExprCore  CoreExpr           -- ^ An expression.
          | AltCore   CoreAlt            -- ^ A case alternative.

-- | TyCo is a universe for use by KURE.  TyCo = Type + Coercion
data TyCo = TypeCore Type                -- ^ A type.
          | CoercionCore Coercion        -- ^ A coercion.

-- | CoreTC is a universe for use by KURE.  CoreTC = Core + TyCo
data CoreTC = Core Core
            | TyCo TyCo

-- QC (for Quantified Clause) is the universe for Quantified + Clause types.
data QC = QCQuantified Quantified
        | QCClause     Clause
        | QCCoreTC     CoreTC

---------------------------------------------------------------------

-- | Alpha equality of 'Core' fragments.
coreAlphaEq :: Core -> Core -> Bool
coreAlphaEq (GutsCore g1) (GutsCore g2) = progAlphaEq (bindsToProg $ mg_binds g1) (bindsToProg $ mg_binds g2)
coreAlphaEq (ProgCore p1) (ProgCore p2) = progAlphaEq p1 p2
coreAlphaEq (BindCore b1) (BindCore b2) = bindAlphaEq b1 b2
coreAlphaEq (DefCore d1)  (DefCore d2)  = defAlphaEq d1 d2
coreAlphaEq (ExprCore e1) (ExprCore e2) = exprAlphaEq e1 e2
coreAlphaEq (AltCore a1)  (AltCore a2)  = altAlphaEq a1 a2
coreAlphaEq _             _             = False

-- | Alpha equality of 'TyCo' fragments.
tyCoAlphaEq :: TyCo -> TyCo -> Bool
tyCoAlphaEq (TypeCore ty1)     (TypeCore ty2)     = typeAlphaEq ty1 ty2
tyCoAlphaEq (CoercionCore co1) (CoercionCore co2) = coercionAlphaEq co1 co2
tyCoAlphaEq _                  _                  = False

-- | Alpha equality of 'CoreTC' fragments.
coreTCAlphaEq :: CoreTC -> CoreTC -> Bool
coreTCAlphaEq (Core c1)  (Core c2)  = coreAlphaEq c1 c2
coreTCAlphaEq (TyCo tc1) (TyCo tc2) = tyCoAlphaEq tc1 tc2
coreTCAlphaEq _          _          = False

---------------------------------------------------------------------

-- | Syntactic equality of 'Core' fragments.
coreSyntaxEq :: Core -> Core -> Bool
coreSyntaxEq (GutsCore g1) (GutsCore g2) = all2 bindSyntaxEq (mg_binds g1) (mg_binds g2)
coreSyntaxEq (ProgCore p1) (ProgCore p2) = progSyntaxEq p1 p2
coreSyntaxEq (BindCore b1) (BindCore b2) = bindSyntaxEq b1 b2
coreSyntaxEq (DefCore d1)  (DefCore d2)  = defSyntaxEq d1 d2
coreSyntaxEq (ExprCore e1) (ExprCore e2) = exprSyntaxEq e1 e2
coreSyntaxEq (AltCore a1)  (AltCore a2)  = altSyntaxEq a1 a2
coreSyntaxEq _             _             = False

-- | Syntactic equality of 'TyCo' fragments.
tyCoSyntaxEq :: TyCo -> TyCo -> Bool
tyCoSyntaxEq (TypeCore ty1)     (TypeCore ty2)     = typeSyntaxEq ty1 ty2
tyCoSyntaxEq (CoercionCore co1) (CoercionCore co2) = coercionSyntaxEq co1 co2
tyCoSyntaxEq _                  _                  = False

-- | Syntactic equality of 'CoreTC' fragments.
coreTCSyntaxEq :: CoreTC -> CoreTC -> Bool
coreTCSyntaxEq (Core c1)  (Core c2)  = coreSyntaxEq c1 c2
coreTCSyntaxEq (TyCo tc1) (TyCo tc2) = tyCoSyntaxEq tc1 tc2
coreTCSyntaxEq _          _          = False

---------------------------------------------------------------------

-- | Find all free variables in a 'Core' node.
freeVarsCore :: Core -> VarSet
freeVarsCore = \case
                  GutsCore g -> freeVarsProg (bindsToProg $ mg_binds g)
                  ProgCore p -> freeVarsProg p
                  BindCore b -> freeVarsBind b
                  DefCore d  -> freeVarsDef d
                  ExprCore e -> freeVarsExpr e
                  AltCore a  -> freeVarsAlt a

-- | Find all free variables in a 'TyCo' node.
freeVarsTyCo :: TyCo -> VarSet
freeVarsTyCo = \case
                  TypeCore ty     -> tyVarsOfType ty
                  CoercionCore co -> tyCoVarsOfCo co

-- | Find all free variables in a 'CoreTC' node.
freeVarsCoreTC :: CoreTC -> VarSet
freeVarsCoreTC = \case
                    TyCo tyco -> freeVarsTyCo tyco
                    Core core -> freeVarsCore core

---------------------------------------------------------------------

instance Injection ModGuts Core where

  inject :: ModGuts -> Core
  inject = GutsCore
  {-# INLINE inject #-}

  project :: Core -> Maybe ModGuts
  project (GutsCore guts) = Just guts
  project _               = Nothing
  {-# INLINE project #-}


instance Injection CoreProg Core where

  inject :: CoreProg -> Core
  inject = ProgCore
  {-# INLINE inject #-}

  project :: Core -> Maybe CoreProg
  project (ProgCore bds) = Just bds
  project _              = Nothing
  {-# INLINE project #-}


instance Injection CoreBind Core where

  inject :: CoreBind -> Core
  inject = BindCore
  {-# INLINE inject #-}

  project :: Core -> Maybe CoreBind
  project (BindCore bnd)  = Just bnd
  project _               = Nothing
  {-# INLINE project #-}


instance Injection CoreDef Core where

  inject :: CoreDef -> Core
  inject = DefCore
  {-# INLINE inject #-}

  project :: Core -> Maybe CoreDef
  project (DefCore def) = Just def
  project _             = Nothing
  {-# INLINE project #-}


instance Injection CoreAlt Core where

  inject :: CoreAlt -> Core
  inject = AltCore
  {-# INLINE inject #-}

  project :: Core -> Maybe CoreAlt
  project (AltCore expr) = Just expr
  project _              = Nothing
  {-# INLINE project #-}


instance Injection CoreExpr Core where

  inject :: CoreExpr -> Core
  inject = ExprCore
  {-# INLINE inject #-}

  project :: Core -> Maybe CoreExpr
  project (ExprCore expr) = Just expr
  project _               = Nothing
  {-# INLINE project #-}

---------------------------------------------------------------------

instance Injection Type TyCo where

  inject :: Type -> TyCo
  inject = TypeCore
  {-# INLINE inject #-}

  project :: TyCo -> Maybe Type
  project (TypeCore ty) = Just ty
  project _             = Nothing
  {-# INLINE project #-}


instance Injection Coercion TyCo where

  inject :: Coercion -> TyCo
  inject = CoercionCore
  {-# INLINE inject #-}

  project :: TyCo -> Maybe Coercion
  project (CoercionCore ty) = Just ty
  project _                 = Nothing
  {-# INLINE project #-}

---------------------------------------------------------------------

instance Injection Core CoreTC where

  inject :: Core -> CoreTC
  inject = Core
  {-# INLINE inject #-}

  project :: CoreTC -> Maybe Core
  project (Core core) = Just core
  project _           = Nothing
  {-# INLINE project #-}


instance Injection TyCo CoreTC where

  inject :: TyCo -> CoreTC
  inject = TyCo
  {-# INLINE inject #-}

  project :: CoreTC -> Maybe TyCo
  project (TyCo tyCo) = Just tyCo
  project _           = Nothing
  {-# INLINE project #-}

---------------------------------------------------------------------

instance Injection ModGuts CoreTC where

  inject :: ModGuts -> CoreTC
  inject = Core . GutsCore
  {-# INLINE inject #-}

  project :: CoreTC -> Maybe ModGuts
  project (Core (GutsCore guts)) = Just guts
  project _                      = Nothing
  {-# INLINE project #-}


instance Injection CoreProg CoreTC where

  inject :: CoreProg -> CoreTC
  inject = Core . ProgCore
  {-# INLINE inject #-}

  project :: CoreTC -> Maybe CoreProg
  project (Core (ProgCore bds)) = Just bds
  project _                     = Nothing
  {-# INLINE project #-}


instance Injection CoreBind CoreTC where

  inject :: CoreBind -> CoreTC
  inject = Core . BindCore
  {-# INLINE inject #-}

  project :: CoreTC -> Maybe CoreBind
  project (Core (BindCore bnd))  = Just bnd
  project _                      = Nothing
  {-# INLINE project #-}


instance Injection CoreDef CoreTC where

  inject :: CoreDef -> CoreTC
  inject = Core . DefCore
  {-# INLINE inject #-}

  project :: CoreTC -> Maybe CoreDef
  project (Core (DefCore def)) = Just def
  project _                    = Nothing
  {-# INLINE project #-}


instance Injection CoreAlt CoreTC where

  inject :: CoreAlt -> CoreTC
  inject = Core . AltCore
  {-# INLINE inject #-}

  project :: CoreTC -> Maybe CoreAlt
  project (Core (AltCore expr)) = Just expr
  project _                     = Nothing
  {-# INLINE project #-}


instance Injection CoreExpr CoreTC where

  inject :: CoreExpr -> CoreTC
  inject = Core . ExprCore
  {-# INLINE inject #-}

  project :: CoreTC -> Maybe CoreExpr
  project (Core (ExprCore expr)) = Just expr
  project _                      = Nothing
  {-# INLINE project #-}


instance Injection Type CoreTC where

  inject :: Type -> CoreTC
  inject = TyCo . TypeCore
  {-# INLINE inject #-}

  project :: CoreTC -> Maybe Type
  project (TyCo (TypeCore ty)) = Just ty
  project _                    = Nothing
  {-# INLINE project #-}


instance Injection Coercion CoreTC where

  inject :: Coercion -> CoreTC
  inject = TyCo . CoercionCore
  {-# INLINE inject #-}

  project :: CoreTC -> Maybe Coercion
  project (TyCo (CoercionCore ty)) = Just ty
  project _                        = Nothing
  {-# INLINE project #-}

---------------------------------------------------------------------

instance Injection Quantified QC where

  inject :: Quantified -> QC
  inject = QCQuantified
  {-# INLINE inject #-}

  project :: QC -> Maybe Quantified
  project (QCQuantified q) = Just q
  project _                = Nothing
  {-# INLINE project #-}

instance Injection Clause QC where

  inject :: Clause -> QC
  inject = QCClause
  {-# INLINE inject #-}

  project :: QC -> Maybe Clause
  project (QCClause cl) = Just cl
  project _             = Nothing
  {-# INLINE project #-}

instance Injection CoreTC QC where

  inject :: CoreTC -> QC
  inject = QCCoreTC
  {-# INLINE inject #-}

  project :: QC -> Maybe CoreTC
  project (QCCoreTC c) = Just c
  project _            = Nothing
  {-# INLINE project #-}

instance Injection Core QC where
  inject :: Core -> QC
  inject = QCCoreTC . inject
  {-# INLINE inject #-}

  project :: QC -> Maybe Core
  project (QCCoreTC c) = project c
  project _            = Nothing
  {-# INLINE project #-}

instance Injection TyCo QC where
  inject :: TyCo -> QC
  inject = QCCoreTC . inject
  {-# INLINE inject #-}

  project :: QC -> Maybe TyCo
  project (QCCoreTC c) = project c
  project _            = Nothing
  {-# INLINE project #-}

instance Injection CoreExpr QC where
  inject :: CoreExpr -> QC
  inject = QCCoreTC . inject
  {-# INLINE inject #-}

  project :: QC -> Maybe CoreExpr
  project (QCCoreTC c) = project c
  project _            = Nothing
  {-# INLINE project #-}

instance Injection CoreBind QC where
  inject :: CoreBind -> QC
  inject = QCCoreTC . inject
  {-# INLINE inject #-}

  project :: QC -> Maybe CoreBind
  project (QCCoreTC c) = project c
  project _            = Nothing
  {-# INLINE project #-}

instance Injection CoreDef QC where
  inject :: CoreDef -> QC
  inject = QCCoreTC . inject
  {-# INLINE inject #-}

  project :: QC -> Maybe CoreDef
  project (QCCoreTC c) = project c
  project _            = Nothing
  {-# INLINE project #-}

instance Injection CoreAlt QC where
  inject :: CoreAlt -> QC
  inject = QCCoreTC . inject
  {-# INLINE inject #-}

  project :: QC -> Maybe CoreAlt
  project (QCCoreTC c) = project c
  project _            = Nothing
  {-# INLINE project #-}

instance Injection Type QC where
  inject :: Type -> QC
  inject = QCCoreTC . inject
  {-# INLINE inject #-}

  project :: QC -> Maybe Type
  project (QCCoreTC c) = project c
  project _            = Nothing
  {-# INLINE project #-}

instance Injection Coercion QC where
  inject :: Coercion -> QC
  inject = QCCoreTC . inject
  {-# INLINE inject #-}

  project :: QC -> Maybe Coercion
  project (QCCoreTC c) = project c
  project _            = Nothing
  {-# INLINE project #-}

---------------------------------------------------------------------

-- | Promote a translate on 'ModGuts'.
promoteModGutsT :: (Monad m, Injection ModGuts g) => Transform c m ModGuts b -> Transform c m g b
promoteModGutsT = promoteWithFailMsgT "This translate can only succeed at the module level."
{-# INLINE promoteModGutsT #-}

-- | Promote a translate on 'CoreProg'.
promoteProgT :: (Monad m, Injection CoreProg g) => Transform c m CoreProg b -> Transform c m g b
promoteProgT = promoteWithFailMsgT "This translate can only succeed at program nodes (the top-level)."
{-# INLINE promoteProgT #-}

-- | Promote a translate on 'CoreBind'.
promoteBindT :: (Monad m, Injection CoreBind g) => Transform c m CoreBind b -> Transform c m g b
promoteBindT = promoteWithFailMsgT "This translate can only succeed at binding group nodes."
{-# INLINE promoteBindT #-}

-- | Promote a translate on 'CoreDef'.
promoteDefT :: (Monad m, Injection CoreDef g) => Transform c m CoreDef b -> Transform c m g b
promoteDefT = promoteWithFailMsgT "This translate can only succeed at recursive definition nodes."
{-# INLINE promoteDefT #-}

-- | Promote a translate on 'CoreAlt'.
promoteAltT :: (Monad m, Injection CoreAlt g) => Transform c m CoreAlt b -> Transform c m g b
promoteAltT = promoteWithFailMsgT "This translate can only succeed at case alternative nodes."
{-# INLINE promoteAltT #-}

-- | Promote a translate on 'CoreExpr'.
promoteExprT :: (Monad m, Injection CoreExpr g) => Transform c m CoreExpr b -> Transform c m g b
promoteExprT = promoteWithFailMsgT "This translate can only succeed at expression nodes."
{-# INLINE promoteExprT #-}

-- | Promote a translate on 'Type'.
promoteTypeT :: (Monad m, Injection Type g) => Transform c m Type b -> Transform c m g b
promoteTypeT = promoteWithFailMsgT "This translate can only succeed at type nodes."
{-# INLINE promoteTypeT #-}

-- | Promote a translate on 'Coercion'.
promoteCoercionT :: (Monad m, Injection Coercion g) => Transform c m Coercion b -> Transform c m g b
promoteCoercionT = promoteWithFailMsgT "This translate can only succeed at coercion nodes."
{-# INLINE promoteCoercionT #-}

-- | Promote a translate on 'Quantified'.
promoteQuantifiedT :: (Monad m, Injection Quantified g) => Transform c m Quantified b -> Transform c m g b
promoteQuantifiedT = promoteWithFailMsgT "This translate can only succeed at quantified nodes."
{-# INLINE promoteQuantifiedT #-}

-- | Promote a translate on 'Clause'.
promoteClauseT :: (Monad m, Injection Clause g) => Transform c m Clause b -> Transform c m g b
promoteClauseT = promoteWithFailMsgT "This translate can only succeed at clause nodes."
{-# INLINE promoteClauseT #-}

-- | Promote a translate on 'Core'.
promoteCoreT :: (Monad m, Injection Core g) => Transform c m Core b -> Transform c m g b
promoteCoreT = promoteWithFailMsgT "This translate can only succeed at core nodes."
{-# INLINE promoteCoreT #-}

-- | Promote a translate on 'CoreTC'.
promoteCoreTCT :: (Monad m, Injection CoreTC g) => Transform c m CoreTC b -> Transform c m g b
promoteCoreTCT = promoteWithFailMsgT "This translate can only succeed at core nodes."
{-# INLINE promoteCoreTCT #-}

---------------------------------------------------------------------

-- | Promote a rewrite on 'ModGuts'.
promoteModGutsR :: (Monad m, Injection ModGuts g) => Rewrite c m ModGuts -> Rewrite c m g
promoteModGutsR = promoteWithFailMsgR "This rewrite can only succeed at the module level."
{-# INLINE promoteModGutsR #-}

-- | Promote a rewrite on 'CoreProg'.
promoteProgR :: (Monad m, Injection CoreProg g) => Rewrite c m CoreProg -> Rewrite c m g
promoteProgR = promoteWithFailMsgR "This rewrite can only succeed at program nodes (the top-level)."
{-# INLINE promoteProgR #-}

-- | Promote a rewrite on 'CoreBind'.
promoteBindR :: (Monad m, Injection CoreBind g) => Rewrite c m CoreBind -> Rewrite c m g
promoteBindR = promoteWithFailMsgR "This rewrite can only succeed at binding group nodes."
{-# INLINE promoteBindR #-}

-- | Promote a rewrite on 'CoreDef'.
promoteDefR :: (Monad m, Injection CoreDef g) => Rewrite c m CoreDef -> Rewrite c m g
promoteDefR = promoteWithFailMsgR "This rewrite can only succeed at recursive definition nodes."
{-# INLINE promoteDefR #-}

-- | Promote a rewrite on 'CoreAlt'.
promoteAltR :: (Monad m, Injection CoreAlt g) => Rewrite c m CoreAlt -> Rewrite c m g
promoteAltR = promoteWithFailMsgR "This rewrite can only succeed at case alternative nodes."
{-# INLINE promoteAltR #-}

-- | Promote a rewrite on 'CoreExpr'.
promoteExprR :: (Monad m, Injection CoreExpr g) => Rewrite c m CoreExpr -> Rewrite c m g
promoteExprR = promoteWithFailMsgR "This rewrite can only succeed at expression nodes."
{-# INLINE promoteExprR #-}

-- | Promote a rewrite on 'Type'.
promoteTypeR :: (Monad m, Injection Type g) => Rewrite c m Type -> Rewrite c m g
promoteTypeR = promoteWithFailMsgR "This rewrite can only succeed at type nodes."
{-# INLINE promoteTypeR #-}

-- | Promote a rewrite on 'Coercion'.
promoteCoercionR :: (Monad m, Injection Coercion g) => Rewrite c m Coercion -> Rewrite c m g
promoteCoercionR = promoteWithFailMsgR "This rewrite can only succeed at coercion nodes."
{-# INLINE promoteCoercionR #-}

-- | Promote a rewrite on 'Quantified'.
promoteQuantifiedR :: (Monad m, Injection Quantified g) => Rewrite c m Quantified -> Rewrite c m g
promoteQuantifiedR = promoteWithFailMsgR "This rewrite can only succeed at quantified nodes."
{-# INLINE promoteQuantifiedR #-}

-- | Promote a rewrite on 'Clause'.
promoteClauseR :: (Monad m, Injection Clause g) => Rewrite c m Clause -> Rewrite c m g
promoteClauseR = promoteWithFailMsgR "This rewrite can only succeed at quantified nodes."
{-# INLINE promoteClauseR #-}

-- | Promote a rewrite on 'Core'.
promoteCoreR :: (Monad m, Injection Core g) => Rewrite c m Core -> Rewrite c m g
promoteCoreR = promoteWithFailMsgR "This rewrite can only succeed at core nodes."
{-# INLINE promoteCoreR #-}

-- | Promote a rewrite on 'CoreTC'.
promoteCoreTCR :: (Monad m, Injection CoreTC g) => Rewrite c m CoreTC -> Rewrite c m g
promoteCoreTCR = promoteWithFailMsgR "This rewrite can only succeed at core nodes."
{-# INLINE promoteCoreTCR #-}

---------------------------------------------------------------------

-- | Promote a bidirectional rewrite on 'CoreExpr'.
promoteExprBiR :: (Monad m, Injection CoreExpr g) => BiRewrite c m CoreExpr -> BiRewrite c m g
promoteExprBiR = promoteWithFailMsgBiR "This rewrite can only succeed at expression nodes."
{-# INLINE promoteExprBiR #-}

---------------------------------------------------------------------
