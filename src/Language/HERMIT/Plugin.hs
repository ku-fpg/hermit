module Language.HERMIT.Plugin (plugin) where

import GhcPlugins
import Control.Monad
import Data.List

import Language.HERMIT.Hermitage as Hermitage
import Language.HERMIT.Pass             -- for now

plugin :: Plugin
plugin = defaultPlugin {
        -- This should get cleaned up at some point
  installCoreToDos = install hermitPass
  }

install :: ([String] -> Hermitage () ModGuts -> IO (Hermitage () ModGuts))
        -> [CommandLineOption]
        -> [CoreToDo] -> CoreM [CoreToDo]
install fn opts todos = do
    liftIO $ print opts
    let filename = "HERMIT.out" -- head $ filter (isSuffixOf ".hermit") opts
        myPass = CoreDoPluginPass "HERMIT" $ \ core0 -> do
                writeProgram ("BEFORE." ++ filename) core0
                core1 <- Hermitage.new (hermitPass opts) core0
                writeProgram ("AFTER." ++ filename) core1
        -- at front, for now
        allPasses = myPass : todos

    reinitializeGlobals
    return allPasses
