{-# LANGUAGE PatternGuards, DataKinds, ScopedTypeVariables #-}

module Language.HERMIT.Plugin.Interactive (plugin) where

import GhcPlugins

import Language.HERMIT.Shell.Command as Dispatch
import Language.HERMIT.Plugin
import System.Console.Haskeline (defaultBehavior)

plugin :: Plugin
plugin = hermitPlugin interactive

interactive :: HermitPass
interactive _opts modGuts = do
    Dispatch.commandLine defaultBehavior modGuts
