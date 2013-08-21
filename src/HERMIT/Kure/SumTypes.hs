{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts, InstanceSigs #-}

module HERMIT.Kure.SumTypes
  ( -- * Sum Types
    Core(..)
  , TyCo(..)
  , CoreTC(..)
  -- * Promotion Combinators
  -- ** Translate Promotions
  , promoteModGutsT
  , promoteProgT
  , promoteBindT
  , promoteDefT
  , promoteExprT
  , promoteAltT
  , promoteTypeT
  , promoteCoercionT
  -- ** Rewrite Promotions
  , promoteModGutsR
  , promoteProgR
  , promoteBindR
  , promoteDefR
  , promoteExprR
  , promoteAltR
  , promoteTypeR
  , promoteCoercionR
  -- ** BiRewrite Promotions
  , promoteExprBiR
  )
where

import GhcPlugins

import Language.KURE.Translate
import Language.KURE.Injection
import Language.KURE.BiTranslate

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

-- | Promote a translate on 'ModGuts'.
promoteModGutsT :: (Monad m, Injection ModGuts g) => Translate c m ModGuts b -> Translate c m g b
promoteModGutsT = promoteWithFailMsgT "This translate can only succeed at the module level."
{-# INLINE promoteModGutsT #-}

-- | Promote a translate on 'CoreProg'.
promoteProgT :: (Monad m, Injection CoreProg g) => Translate c m CoreProg b -> Translate c m g b
promoteProgT = promoteWithFailMsgT "This translate can only succeed at program nodes (the top-level)."
{-# INLINE promoteProgT #-}

-- | Promote a translate on 'CoreBind'.
promoteBindT :: (Monad m, Injection CoreBind g) => Translate c m CoreBind b -> Translate c m g b
promoteBindT = promoteWithFailMsgT "This translate can only succeed at binding group nodes."
{-# INLINE promoteBindT #-}

-- | Promote a translate on 'CoreDef'.
promoteDefT :: (Monad m, Injection CoreDef g) => Translate c m CoreDef b -> Translate c m g b
promoteDefT = promoteWithFailMsgT "This translate can only succeed at recursive definition nodes."
{-# INLINE promoteDefT #-}

-- | Promote a translate on 'CoreAlt'.
promoteAltT :: (Monad m, Injection CoreAlt g) => Translate c m CoreAlt b -> Translate c m g b
promoteAltT = promoteWithFailMsgT "This translate can only succeed at case alternative nodes."
{-# INLINE promoteAltT #-}

-- | Promote a translate on 'CoreExpr'.
promoteExprT :: (Monad m, Injection CoreExpr g) => Translate c m CoreExpr b -> Translate c m g b
promoteExprT = promoteWithFailMsgT "This translate can only succeed at expression nodes."
{-# INLINE promoteExprT #-}

-- | Promote a translate on 'Type'.
promoteTypeT :: (Monad m, Injection Type g) => Translate c m Type b -> Translate c m g b
promoteTypeT = promoteWithFailMsgT "This translate can only succeed at type nodes."
{-# INLINE promoteTypeT #-}

-- | Promote a translate on 'Coercion'.
promoteCoercionT :: (Monad m, Injection Coercion g) => Translate c m Coercion b -> Translate c m g b
promoteCoercionT = promoteWithFailMsgT "This translate can only succeed at coercion nodes."
{-# INLINE promoteCoercionT #-}

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

---------------------------------------------------------------------

-- | Promote a bidirectional rewrite on 'CoreExpr'.
promoteExprBiR :: (Monad m, Injection CoreExpr g) => BiRewrite c m CoreExpr -> BiRewrite c m g
promoteExprBiR b = bidirectional (promoteExprR $ forewardT b) (promoteExprR $ backwardT b)
{-# INLINE promoteExprBiR #-}

---------------------------------------------------------------------
