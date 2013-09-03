module HERMIT (plugin) where

import HERMIT.GHC
import HERMIT.Optimize

plugin :: Plugin
plugin = optimize $ \ options -> phase 0 $ interactive [] options
