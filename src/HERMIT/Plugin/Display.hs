{-# LANGUAGE FlexibleContexts #-}
module HERMIT.Plugin.Display
    ( display
    , ps_putStr
    , ps_putStrLn
    ) where

import Control.Monad.State

import Data.Maybe (fromMaybe)
import Data.Monoid

import HERMIT.Kernel (queryK)
import HERMIT.Kure
import HERMIT.Plugin.Types
import HERMIT.PrettyPrinter.Common

import System.IO

display :: Maybe PathH -> PluginM ()
display window = do
    st <- get
    let k = ps_kernel st
        ast = ps_cursor st
        ppOpts = pOptions $ ps_pretty st
    d <- queryK k (extractT $ pathT (fromMaybe mempty window) $ liftPrettyH ppOpts $ pCoreTC $ ps_pretty st)
                Nothing (mkKernelEnv st) ast
    liftIO $ ps_render st stdout ppOpts $ Right $ snd d -- discard new AST, assuming pretty printer won't create one

ps_putStr :: (MonadIO m, MonadState PluginState m) => String -> m ()
ps_putStr str = do
    st <- get
    liftIO $ ps_render st stdout (pOptions $ ps_pretty st) (Left str)

ps_putStrLn :: (MonadIO m, MonadState PluginState m) => String -> m ()
ps_putStrLn = ps_putStr . (++"\n")

