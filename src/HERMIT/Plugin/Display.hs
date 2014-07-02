{-# LANGUAGE CPP, FlexibleContexts #-}
module HERMIT.Plugin.Display
    ( display
    , getFocusPath
    , ps_putStr
    , ps_putStrLn
    ) where

import Control.Monad.State

import Data.Maybe (fromMaybe)

#if __GLASGOW_HASKELL__ >= 708 && defined(mingw32_HOST_OS)
import HERMIT.GHC (resetStaticOpts)
#endif
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
        ppOpts = (pOptions $ ps_pretty st) { po_focus = Just focusPath }
#if __GLASGOW_HASKELL__ >= 708 && defined(mingw32_HOST_OS)
    liftIO resetStaticOpts
#endif
    iokm' "Rendering error: "
        (liftIO . ps_render st stdout ppOpts . Right)
        (toASTS skernel (ps_cursor st) >>= \ ast ->
            queryK (kernelS skernel) ast (extractT $ pathT (fromMaybe focusPath window) $ liftPrettyH ppOpts $ pCoreTC $ ps_pretty st) (mkKernelEnv st))

ps_putStr :: (MonadIO m, MonadState PluginState m) => String -> m ()
ps_putStr str = do
    st <- get
    liftIO $ ps_render st stdout (pOptions $ ps_pretty st) (Left str)

ps_putStrLn :: (MonadIO m, MonadState PluginState m) => String -> m ()
ps_putStrLn = ps_putStr . (++"\n")

