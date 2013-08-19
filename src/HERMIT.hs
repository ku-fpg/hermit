module HERMIT (plugin) where

import GhcPlugins

import HERMIT.Optimize

plugin :: Plugin
plugin = optimize $ \ options -> phase 0 $ interactive [] options
