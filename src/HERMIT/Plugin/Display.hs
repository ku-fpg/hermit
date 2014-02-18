{-# LANGUAGE FlexibleContexts #-}
module HERMIT.Plugin.Display
    ( display
    , getFocusPath
    , ps_putStr
    , ps_putStrLn
    ) where

import Control.Monad.State

import Data.Maybe (fromMaybe)

import HERMIT.Kernel (queryK)
import HERMIT.Kernel.Scoped
import HERMIT.Kure
import HERMIT.Plugin.Types
import HERMIT.PrettyPrinter.Common

import System.IO

getFocusPath :: PluginM PathH
getFocusPath = get >>= \ st -> liftM concat $ prefixFailMsg "getFocusPath - pathS failed: " $ pathS (ps_kernel st) (ps_cursor st)

display :: Maybe PathH -> PluginM ()
display window = do
    st <- get
    focusPath <- getFocusPath
    let skernel = ps_kernel st
        ppOpts = (ps_pretty_opts st) { po_focus = Just focusPath }
    -- Do not show focus while loading
    ifM (gets ps_running_script)
        (return ())
        (iokm' "Rendering error: "
               (liftIO . ps_render st stdout ppOpts . Right)
               (toASTS skernel (ps_cursor st) >>= \ ast ->
                    queryK (kernelS skernel) ast (extractT $ pathT (fromMaybe focusPath window) $ liftPrettyH ppOpts $ ps_pretty st) (mkKernelEnv st))
        )

ps_putStr :: (MonadIO m, MonadState PluginState m) => String -> m ()
ps_putStr str = do
    st <- get
    liftIO $ ps_render st stdout (ps_pretty_opts st) (Left str)

ps_putStrLn :: (MonadIO m, MonadState PluginState m) => String -> m ()
ps_putStrLn = ps_putStr . (++"\n")

