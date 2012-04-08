{-# LANGUAGE KindSignatures, GADTs #-}

module Language.HERMIT.Command
        ( Command(..)
        ) where

import Language.HERMIT.Types

-- | 'Command' is what you send to the HERMIT kernel.
data Command :: * where
   Apply        :: Rewrite Blob         -> Command
   PushFocus    :: Lens Blob Blob       -> Command
   PopFocus                             :: Command
   ResetFocus                           :: Command
   Message      :: String               -> Command

