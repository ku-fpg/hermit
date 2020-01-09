module HERMIT.Exception
  where

import           Control.Exception hiding (catch)

import           Language.KURE.MonadCatch

-- newtype HException = HException {unHException :: String}

-- newtype HException = HException {unHException :: SomeException}

-- instance Show HException where
--   show = unHException

-- instance Exception HException

-- modMsgException :: (String -> String) -> HException -> HException
-- modMsgException f (HException str) = HException (f str)

-- modFailMsg :: MonadCatch m => (String -> String) -> m a -> m a
-- modFailMsg f ma = ma `catch` \me@HException{} -> throwM (modMsgException f me)

