{-# LANGUAGE PatternGuards #-}

module Language.HERMIT.Pass (hermitPass, ppProgram, writeProgram) where

import GhcPlugins
import PprCore -- compiler/coreSyn/PprCore.lhs

import Control.Monad

import Language.HERMIT.Hermitage as Hermitage
import Language.HERMIT.CommandLine as CommandLine

hermitPass :: [String] -> Hermitage () ModGuts -> CoreM (Hermitage () ModGuts)
-- run the command-line option
hermitPass ["cl"]  h      = do
        liftIO $ print "command line!"
        CommandLine.commandLine h
-- find a function, interprete it (TODO)
hermitPass ['@':nm]  h    = return h
-- Need better error message here
hermitPass other        h = error $ "hermitPass failed" ++ show other

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
