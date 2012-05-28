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
    let (modes, opts') = partition (isPrefixOf "mode=") opts
        myPass = CoreDoPluginPass "HERMIT" $ parseMode modes opts'
        -- at front, for now
        allPasses = myPass : todos

    reinitializeGlobals
    return allPasses

parseMode :: [CommandLineOption] -> HermitPass
parseMode mStr = head [ p | (n,p) <- passes_dict, n `elem` modes ]
    where modes = mapM (fromJust . stripPrefix "mode=") mStr
