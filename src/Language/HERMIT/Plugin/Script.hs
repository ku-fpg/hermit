{-# LANGUAGE PatternGuards, DataKinds, ScopedTypeVariables #-}

module Language.HERMIT.Plugin.Script (plugin) where

import GhcPlugins

import Language.HERMIT.Shell.Command as Dispatch
import Language.HERMIT.Plugin

import System.Console.Haskeline (useFile)

plugin :: Plugin
plugin = hermitPlugin scripted

scripted :: HermitPass
scripted opts modGuts =
    case opts of
        [ ('/' : filename) ] -> do
            Dispatch.commandLine (useFile filename) modGuts
        _ -> return modGuts
