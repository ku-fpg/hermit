{-# LANGUAGE KindSignatures, GADTs #-}

module Language.HERMIT.Command
        ( Command(..)
        , runCommands
        ) where

import GhcPlugins

import Language.KURE

import Language.HERMIT.Types
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


runCommands
        :: (HermitEnv -> Core -> IO Command)                 -- waiting for commands
        -> (String -> IO ())                            -- where to send errors
        -> ModGuts -> CoreM ModGuts
runCommands getCmd errorMsg modGuts = do
        (_, ModGutsCore modGuts') <- loop initHermitEnv (ModGutsCore modGuts)
        return modGuts'
 where
    loop :: HermitEnv -> Core -> CoreM (HermitEnv,Core)
    loop c b = do
        rep <- liftIO $ getCmd c b
        case rep of
           PopFocus -> return (c,b)
           PushFocus lens -> do
                res <- runHermitM (apply lens c b)
                case res of
                  FailR msg -> do
                     liftIO $ errorMsg $ show msg
                     loop c b
                  SuccessR ((c1,b1),kick) -> do
                     (c2, b2) <- loop c1 b1
                     res2 <- runHermitM (kick b2)
                     case res2 of
                        FailR msg -> do
                           liftIO $ errorMsg $ show msg
                           -- Opps, use the original context because failed to kick
                           loop c b
                        SuccessR b3 -> do
                           -- Remember, the Context never changes at a specific depth
                           loop c2 b3 -- Check that you meant c2 here, you shadowed a variable originally and I'm not sure if that was a mistake.
           Apply rr -> do
                res <- runHermitM (apply rr c b)
                case res of
                  FailR msg -> do
                     liftIO $ errorMsg $ show msg
                     loop c b
                  SuccessR b' -> do
                     loop c b'
