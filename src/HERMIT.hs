module HERMIT (plugin) where

import GhcPlugins

import Language.HERMIT.Optimize

plugin :: Plugin
plugin = optimize $ \ options -> phase 0 $ interactive [] options
