{-# LANGUAGE DataKinds #-}

module Language.HERMIT.Plugin (plugin) where

import GhcPlugins
import Data.List
import Data.Maybe (fromJust)

import Language.HERMIT.Plugin.Common

import qualified Language.HERMIT.Plugin.CommandLine as CommandLine
import qualified Language.HERMIT.Plugin.Restful as Restful

passes_dict :: [NamedPass]
passes_dict = CommandLine.passes
           ++ Restful.passes

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todos = do
    liftIO $ print opts
    let myPass = CoreDoPluginPass "HERMIT" $ modFilter opts
        -- at front, for now
        allPasses = myPass : todos

    reinitializeGlobals
    return allPasses

-- | Determine whether to act on this module, choose plugin pass.
modFilter :: HermitPass
modFilter allOpts guts | null modOpts = return guts -- don't process this module
                       | otherwise    = pass
    where modOpts = filterOpts allOpts guts
          pass = uncurry parseMode (partition (isPrefixOf "mode=") modOpts) guts

-- | Filter options to those pertaining to this module, stripping module prefix.
filterOpts :: [CommandLineOption] -> ModGuts -> [CommandLineOption]
filterOpts opts guts = [ drop len nm | nm <- opts, modName `isPrefixOf` nm ]
    where modName = showSDoc (ppr (mg_module guts))
          len = length modName + 1 -- for the colon

-- | Pick plugin pass based on mode option.
parseMode :: [CommandLineOption] -> HermitPass
parseMode ms | null passes = error "HERMIT: no mode flag"
             | otherwise   = head passes
    where passes = [ p | (n,p) <- passes_dict, n `elem` modes ]
          modes = mapM (fromJust . stripPrefix "mode=") ms

