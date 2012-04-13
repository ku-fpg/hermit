{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

module Language.HERMIT.HermitMonad where

import GhcPlugins hiding (empty)

import MonadUtils       -- from GHC
import Control.Monad

import Control.Applicative

----------------------------------------------------------------------------

-- | The transformation/HERMIT monad
newtype HermitM a = HermitM { runHermitM :: CoreM (HermitR a) }

data HermitR a = SuccessR a | FailR String
                 deriving (Eq,Show)

runHermitR :: (a -> b) -> (String -> b) -> HermitR a -> b
runHermitR s _ (SuccessR a) = s a
runHermitR _ f (FailR msg)  = f msg


instance Functor HermitR where
  fmap f = runHermitR (SuccessR . f) FailR 
  
instance Functor HermitM where
  fmap f (HermitM mha) = HermitM ((fmap.fmap) f mha)


instance Applicative HermitR where
  pure = SuccessR
  rf <*> ra = runHermitR (<$> ra) FailR rf
  
instance Applicative HermitM where
  pure  = HermitM . pure . pure
  (HermitM f) <*> (HermitM a) = HermitM (liftA2 (<*>) f a)




instance MonadIO HermitM where
        liftIO = liftCoreM . liftIO

instance MonadUnique HermitM where
        getUniqueSupplyM = liftCoreM $ getUniqueSupplyM

liftCoreM :: CoreM a -> HermitM a
liftCoreM m = HermitM $ do r <- m
                           return $ SuccessR r





instance Alternative HermitR where
  empty = FailR ""
  ra <|> rb = catchHR ra (const rb) 
  
instance Alternative HermitM where  
  empty = HermitM (pure empty)
  (HermitM a) <|> (HermitM b) = HermitM (liftA2 (<|>) a b) -- only catch 'empty's in HermitR, not in CoreM


instance Monad HermitR where
  return = pure
  ra >>= f = runHermitR f FailR ra
  fail = FailR
  
instance Monad HermitM where  
  return = pure
  (HermitM mra) >>= f = HermitM (mra >>= runHermitR (runHermitM.f) (return.FailR))
  fail = HermitM . return . FailR  -- I've used FailR instead of fail as I'm worried that "return . fail" could lead to ambiguity


-- These are the methods that are neccassary to make instances of Monad.Error

catchHR :: HermitR a -> (String -> HermitR a) -> HermitR a
catchHR ra f = runHermitR SuccessR f ra

catchH :: HermitM a -> (String -> HermitM a) -> HermitM a
catchH (HermitM mra) f = HermitM (mra >>= runHermitR (return.SuccessR) (runHermitM.f))

