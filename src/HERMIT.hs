module HERMIT (plugin) where

import Data.Maybe (fromMaybe)

import HERMIT.GHC
import HERMIT.Plugin.Builder (getPhaseFlag)
import HERMIT.Plugin

plugin :: Plugin
plugin = hermitPlugin $ \ options -> let (pn,opts) = fromMaybe (0,options) (getPhaseFlag options)
                                     in phase pn $ interactive [] opts
