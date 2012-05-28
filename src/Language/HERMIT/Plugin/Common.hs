module Language.HERMIT.Plugin.Common where

import GhcPlugins

type NamedPass = (String, HermitPass)
type HermitPass = [CommandLineOption] -> ModGuts -> CoreM ModGuts
