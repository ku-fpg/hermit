module HERMIT (plugin) where

import Data.List (isPrefixOf)

import HERMIT.GHC
import HERMIT.Optimize

plugin :: Plugin
plugin = optimize $ \ options -> let pn = case filter ("-p" `isPrefixOf`) options of
                                            [] -> 0
                                            (('-':'p':num):_) -> read num
                                 in phase pn $ interactive [] options
