module HERMIT (plugin) where

import Data.Maybe (fromMaybe)

import HERMIT.GHC
import HERMIT.Plugin.Builder (getPassFlag)
import HERMIT.Plugin

plugin :: Plugin
plugin = hermitPlugin $ \ options -> let (pn,opts) = fromMaybe (0,options) (getPassFlag options)
                                     in pass pn $ interactive [] opts
