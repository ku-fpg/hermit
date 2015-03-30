{-# LANGUAGE FlexibleContexts #-}
module HERMIT.Plugin.Display
    ( display
    , ps_putStr
    , ps_putStrLn
    ) where

import Control.Monad.Reader
import Control.Monad.State

import Data.Maybe (fromMaybe)
import Data.Monoid

import HERMIT.Kernel (queryK, CommitMsg(..))
import HERMIT.Kure
import HERMIT.Plugin.Types
import HERMIT.PrettyPrinter.Common

import System.IO

display :: Maybe Handle -> Maybe PathH -> PluginM ()
display mbh window = do
    k <- asks pr_kernel
    st <- get
    let ast = ps_cursor st
        ppOpts = pOptions $ ps_pretty st
        h = fromMaybe stdout mbh
    d <- queryK k (extractT $ pathT (fromMaybe mempty window) $ liftPrettyH ppOpts $ pCoreTC $ ps_pretty st)
                Never (mkKernelEnv st) ast
    liftIO $ ps_render st h ppOpts $ Right $ snd d -- discard new AST, assuming pretty printer won't create one

ps_putStr :: (MonadIO m, MonadState PluginState m) => String -> m ()
ps_putStr str = do
    st <- get
    liftIO $ ps_render st stdout (pOptions $ ps_pretty st) (Left str)

ps_putStrLn :: (MonadIO m, MonadState PluginState m) => String -> m ()
ps_putStrLn = ps_putStr . (++"\n")

