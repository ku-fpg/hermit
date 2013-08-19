{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, InstanceSigs #-}

module HERMIT.Kure.SumTypes
  ( -- * Sum Types
    Core(..)
  , TyCo(..)
  , CoreTC(..)
  )
where

import GhcPlugins

import Language.KURE.Injection

import HERMIT.Core

---------------------------------------------------------------------

-- | Core is a sum type for use by KURE.  Core = ModGuts + CoreProg + CoreBind + CoreDef + CoreExpr + CoreAlt
data Core = GutsCore  ModGuts            -- ^ The module.
          | ProgCore  CoreProg           -- ^ A program (a telescope of top-level binding groups).
          | BindCore  CoreBind           -- ^ A binding group.
          | DefCore   CoreDef            -- ^ A recursive definition.
          | ExprCore  CoreExpr           -- ^ An expression.
          | AltCore   CoreAlt            -- ^ A case alternative.

-- | TyCo is a sum type for use by KURE.  TyCo = Type + Coercion
data TyCo = TypeCore Type                -- ^ A type.
          | CoercionCore Coercion        -- ^ A coercion.

-- | CoreTC is a sum type for use by KURE.  CoreTC = Core + TyCo
data CoreTC = Core Core
            | TyCo TyCo

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
