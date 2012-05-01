{-# LANGUAGE KindSignatures, GADTs #-}

module Language.HERMIT.Command
        ( Command(..)
        , runCommands
        ) where

import GhcPlugins

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad

-- | 'Command' is what you send to the HERMIT kernel.
data Command :: * where
   Apply        :: RewriteH Core        -> Command
   PushFocus    :: LensH Core Core      -> Command
   PopFocus                             :: Command
   ResetFocus                           :: Command
   Message      :: String               -> Command

instance Show Command where
   show (Apply _)       = "Apply -"
   show (PushFocus _)   = "PushFocus -"
   show (PopFocus)      = "PopFocus"
   show (ResetFocus)    = "ResetFocus"
   show (Message _)     = "Message"


runCommands :: (HermitEnv -> Core -> IO Command)  -- waiting for commands
            -> (String -> IO ())                  -- where to send errors
            -> ModGuts -> CoreM ModGuts
runCommands getCommand errMsg modGuts = do
        ModGutsCore modGuts' <- loop initHermitEnv (ModGutsCore modGuts)
        return modGuts'
  where
    loop :: HermitEnv -> Core -> CoreM Core
    loop c a = do
        rep <- liftIO (getCommand c a)
        case rep of
           Apply rr    -> runHermitMR (loop c) abort (apply rr c a)
           PopFocus    -> return a
           PushFocus l -> runHermitMR (\ ((cb,b),kick) -> do b' <- loop cb b
                                                             runHermitMR (loop c) abort (kick b')
                                      ) 
                                      abort 
                                      (apply l c a)  
           -- ResetFocus  -> ?
           -- Message msg -> ?
      where
        -- The argument String is the field of FailR in the HermitR monad.
        abort :: String -> CoreM Core
        abort msg = liftIO (errMsg msg) >> loop c a