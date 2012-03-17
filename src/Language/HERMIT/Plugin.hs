module Language.HERMIT.Plugin (plugin) where

import GhcPlugins
import Control.Monad
import Data.List

import Language.HERMIT.Pass

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install opts todos = do
    liftIO $ print opts
    let filename = head $ filter (isSuffixOf ".hermit") opts
        myPass = CoreDoPluginPass "PrintCore" $ writeProgram filename
        allPasses = if (elem  "back" opts)
                    then todos ++ [myPass]
                    else myPass : todos

    reinitializeGlobals
    return allPasses
