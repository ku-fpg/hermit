{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

module Language.HERMIT.HermitMonad where

import GhcPlugins
import qualified Data.Map as Map
import Control.Monad

----------------------------------------------------------------------------
-- The transformation/HERMIT monad
data HermitM a = HermitM (CoreM a)
               | FailM String

instance Monad HermitM where
        return a = HermitM (return a)
        (HermitM m) >>= k = HermitM $ do
                r <- m
                case k r of
                  HermitM m' -> m'
        (FailM msg) >>= _ = FailM msg
        fail msg = FailM msg

catchH :: HermitM a -> (String -> HermitM a) -> HermitM a
catchH (HermitM m) k = HermitM m
catchH (FailM msg) k = k msg

----------------------------------------------------------------------------

runHermitM :: HermitM a -> CoreM (Either String a)
runHermitM (HermitM m) = liftM Right m
runHermitM (FailM str) = return $ Left str