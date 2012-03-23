{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

module Language.HERMIT.HermitMonad where

import GhcPlugins
import qualified Data.Map as Map

----------------------------------------------------------------------------
-- The transformation/HERMIT monad
newtype HermitM a = HermitM a    -- id, for now

instance Monad HermitM where
        return a = HermitM a

----------------------------------------------------------------------------
