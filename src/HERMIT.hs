module HERMIT (plugin) where

import Data.List (isPrefixOf)
import Data.Maybe (fromMaybe)

import HERMIT.GHC
import HERMIT.Optimize
import HERMIT.Plugin (getPhaseFlag)

plugin :: Plugin
plugin = optimize $ \ options -> let (pn,opts) = fromMaybe (0,options) (getPhaseFlag options)
                                 in phase pn $ interactive [] opts
