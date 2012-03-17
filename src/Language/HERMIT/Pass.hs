{-# LANGUAGE PatternGuards #-}

module Language.HERMIT.Pass (ppProgram, writeProgram) where

import GhcPlugins
import PprCore -- compiler/coreSyn/PprCore.lhs

import Control.Monad

ppProgram :: ModGuts -> CoreM ModGuts
ppProgram = bindsOnlyPass printBinds

printBinds :: CoreProgram -> CoreM CoreProgram
printBinds binds  = do
  putMsg $ pprCoreBindings binds
  return $ binds

writeProgram :: FilePath -> ModGuts -> CoreM ModGuts
writeProgram filename =
    bindsOnlyPass (\binds -> do liftIO $ writeFile filename $ showSDoc $ pprCoreBindings binds
                                return binds)
