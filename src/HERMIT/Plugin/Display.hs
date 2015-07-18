{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoImplicitPrelude #-}

module HERMIT.Plugin.Display
    ( showDisplay
    , printDisplay
    , ps_putStr
    , ps_putStrLn
    ) where

import Control.Monad.Reader
import Control.Monad.State

import Data.Maybe (fromMaybe)

import HERMIT.Kernel (queryK, CommitMsg(..))
import HERMIT.Kure
import HERMIT.Plugin.Types
import HERMIT.PrettyPrinter.Common

import Prelude.Compat

import System.IO

showDisplay :: Maybe PathH -> PluginM DocH
showDisplay window = do
    k <- asks pr_kernel
    st <- get
    let ast = ps_cursor st
        ppOpts = pOptions $ ps_pretty st
    d <- queryK k (extractT $ pathT (fromMaybe mempty window) $ liftPrettyH ppOpts $ pCoreTC $ ps_pretty st)
                Never (mkKernelEnv st) ast
    return $ snd d -- discard new AST, assuming pretty printer won't create one

-- TODO: rm
printDisplay :: Maybe Handle -> Maybe PathH -> PluginM ()
printDisplay mbh window = do
    doc <- showDisplay window 
    st <- get
    let ppOpts = pOptions $ ps_pretty st
        h = fromMaybe stdout mbh
    liftIO $ ps_render st h ppOpts $ Right $ doc

-- TODO: rm
ps_putStr :: (MonadIO m, MonadState PluginState m) => String -> m ()
ps_putStr str = do
    st <- get
    liftIO $ ps_render st stdout (pOptions $ ps_pretty st) (Left str)

-- TODO: rm
ps_putStrLn :: (MonadIO m, MonadState PluginState m) => String -> m ()
ps_putStrLn = ps_putStr . (++"\n")

