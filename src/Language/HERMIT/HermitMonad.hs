{-# LANGUAGE TypeFamilies, FlexibleInstances, GADTs #-}
-- TODO: remove this module

module Language.HERMIT.HermitMonad where

import GhcPlugins
import MonadUtils       -- from GHC
import qualified Data.Map as Map
import Control.Monad

----------------------------------------------------------------------------
-- The transformation/HERMIT monad
newtype HermitM a = HermitM { runHermitM :: CoreM (HermitR a) }

data HermitR :: * -> * where
        SuccessR :: a                   -> HermitR a
        FailR    :: String               -> HermitR a

instance Monad HermitM where
        return a = HermitM (return $ SuccessR a)
        (HermitM m) >>= k = HermitM $ do
                r <- m
                case r of
                  SuccessR a -> runHermitM (k a)
                  FailR msg  -> return $ FailR msg
        fail msg = HermitM (return $ FailR msg)

catchH :: HermitM a -> (String -> HermitM a) -> HermitM a
catchH (HermitM m) k = HermitM $ do
        r <- m
        case r of
          SuccessR a -> return $ SuccessR a
          FailR msg  -> runHermitM (k msg)

instance MonadIO HermitM where
        liftIO = liftCoreM . liftIO

instance MonadUnique HermitM where
        getUniqueSupplyM = liftCoreM $ getUniqueSupplyM

liftCoreM :: CoreM a -> HermitM a
liftCoreM m = HermitM $ do r <- m
                           return $ SuccessR r
