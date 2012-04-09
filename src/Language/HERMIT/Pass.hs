{-# LANGUAGE PatternGuards, DataKinds #-}

module Language.HERMIT.Pass (hermitPass, ppProgram, writeProgram) where

import GhcPlugins
import PprCore -- compiler/coreSyn/PprCore.lhs

import Data.List
import Control.Monad

import Language.HERMIT.CommandLine as CommandLine


-- Syntax:
--   FullModuleName(filename),    <-- reads Module.hermit
--   FullModuleName(-)            <-- starts the interpreter

hermitPass :: [String] -> ModGuts -> CoreM ModGuts
-- run the command-line option
hermitPass nms modGuts = case candidates of
        [ ('/' : '-': []) ] -> do
                CommandLine.commandLine modGuts
        _ -> return modGuts
   where
           modName = showSDoc (ppr (mg_module modGuts))
           candidates = [ drop (length modName) nm
                        | nm <- nms
                        , modName `isPrefixOf` nm
                        ]
{-        --
-- find a function, interprete it (TODO)
hermitPass ['@':nm]  h    = return h
-- Need better error message here
hermitPass other        h = error $ "hermitPass failed" ++ show other
-}
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
