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
   Apply        :: RewriteH Core            -> Command
   Query        :: TranslateH Core String   -> Command
   PushFocus    :: LensH Core Core          -> Command
   PopFocus                                 :: Command
   ResetFocus                               :: Command
   Message      :: String                   -> Command

instance Show Command where
   show (Apply _)       = "Apply -"
   show (PushFocus _)   = "PushFocus -"
   show (PopFocus)      = "PopFocus"
   show (ResetFocus)    = "ResetFocus"
   show (Message _)     = "Message"


runCommands :: (HermitEnv -> Core -> IO Command)  -- waiting for commands
            -> (String -> IO ())                  -- where to send output
            -> ModGuts -> CoreM ModGuts
runCommands getCommand output modGuts = do
        ModGutsCore modGuts' <- loop initHermitEnv (ModGutsCore modGuts)
        return modGuts'
  where
    loop :: HermitEnv -> Core -> CoreM Core
    loop c a = do
        rep <- liftIO (getCommand c a)
        case rep of
           Apply rr    -> runHermitMR (loop c) printAndLoop (apply rr c a)
           Query tt    -> runHermitMR printAndLoop printAndLoop (apply tt c a)
           PopFocus    -> return a
           PushFocus l -> runHermitMR (\ ((cb,b),kick) -> do b' <- loop cb b
                                                             runHermitMR (loop c) printAndLoop (kick b')
                                      ) 
                                      printAndLoop
                                      (apply l c a)  
           -- ResetFocus  -> ?
           -- Message msg -> ?
      where
        printAndLoop :: String -> CoreM Core
        printAndLoop s = liftIO (output s) >> loop c a