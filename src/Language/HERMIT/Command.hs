{-# LANGUAGE KindSignatures, GADTs #-}

module Language.HERMIT.Command
        ( Command(..)
        , runCommands
        ) where

import GhcPlugins

import Language.HERMIT.Types
import Language.HERMIT.KURE
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad

-- | 'Command' is what you send to the HERMIT kernel.
data Command :: * where
   Apply        :: Rewrite Core         -> Command
   PushFocus    :: Lens Core Core       -> Command
   PopFocus                             :: Command
   ResetFocus                           :: Command
   Message      :: String               -> Command

runCommands
        :: (Context Core -> IO Command)                 -- waiting for commands
        -> (String -> IO ())                            -- where to send errors
        -> ModGuts -> CoreM ModGuts
runCommands getCmd errorMsg modGuts = do
        Context _ (ModGutsCore modGuts') <- loop (Context initHermitEnv (ModGutsCore modGuts))
        return modGuts'
 where
    loop :: Context Core -> CoreM (Context Core)
    loop cxt@(Context c b) = do
        rep <- liftIO $ getCmd cxt
        case rep of
           PopFocus -> return cxt
           PushFocus lens -> do
                res <- runHermitM (apply lens cxt)
                case res of
                  FailR msg -> do
                     liftIO $ errorMsg $ show msg
                     loop cxt
                  SuccessR (cxt1,kick) -> do
                     cxt2@(Context c b2) <- loop cxt1
                     res2 <- runHermitM (kick b2)
                     case res2 of
                        FailR msg -> do
                           liftIO $ errorMsg $ show msg
                           -- Opps, use the original context because failed to kick
                           loop cxt
                        SuccessR b3 -> do
                           -- Remember, the Context never changes at a specific depth
                           loop (Context c b3)
           Apply rr -> do
                res <- runHermitM (apply rr cxt)
                case res of
                  FailR msg -> do
                     liftIO $ errorMsg $ show msg
                     loop cxt
                  SuccessR b' -> do
                     loop (Context c b')
