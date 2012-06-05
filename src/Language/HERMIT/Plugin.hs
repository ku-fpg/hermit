{-# LANGUAGE DataKinds #-}

module Language.HERMIT.Plugin (HermitPass, hermitPlugin) where

import GhcPlugins
import Data.List

type HermitPass = [CommandLineOption] -> ModGuts -> CoreM ModGuts

-- Build a hermit plugin. This mainly handles the per-module options.
hermitPlugin :: HermitPass -> Plugin
hermitPlugin hp = defaultPlugin { installCoreToDos = install }
    where
        install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
        install opts todos = do
            liftIO $ print opts
            let
                myPass = CoreDoPluginPass "HERMIT" $ modFilter hp opts
                -- at front, for now
                allPasses = myPass : todos

            reinitializeGlobals
            return allPasses

-- | Determine whether to act on this module, choose plugin pass.
modFilter :: HermitPass -> HermitPass
modFilter hp opts guts | null modOpts = return guts -- don't process this module
                       | otherwise    = hp modOpts guts
    where modOpts = filterOpts opts guts

-- | Filter options to those pertaining to this module, stripping module prefix.
filterOpts :: [CommandLineOption] -> ModGuts -> [CommandLineOption]
filterOpts opts guts = [ drop len nm | nm <- opts, modName `isPrefixOf` nm ]
    where modName = showSDoc (ppr (mg_module guts))
          len = length modName + 1 -- for the colon
