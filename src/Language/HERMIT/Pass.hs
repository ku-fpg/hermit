{-# LANGUAGE PatternGuards, DataKinds, ScopedTypeVariables #-}

module Language.HERMIT.Pass (hermitPass, ppProgram, writeProgram) where

import GhcPlugins
import PprCore -- compiler/coreSyn/PprCore.lhs

--import System.Console.Editline

import Data.List
import Control.Monad
import System.IO

-- The Prelude version of catch has been deprecated.
import Prelude hiding (catch)
import Control.Exception (catch, SomeException)

import Language.HERMIT.Shell.Dispatch as CommandLine
import System.Console.Getline

-- Syntax:
--   FullModuleName(filename),    <-- reads Module.hermit
--   FullModuleName(-)            <-- starts the interpreter

hermitPass :: [String] -> ModGuts -> CoreM ModGuts
-- run the command-line option
hermitPass nms modGuts = case candidates of
        [ ('/' : '-': []) ] -> do

                elGets <- liftIO getEditor

                let append = appendFile ".hermitlog"
                liftIO $ append "\n-- starting new session\n"
                let get = do str <- elGets "hermit> "
                             case str of
                               Nothing -> do append "-- ^D\n"
                                             return Nothing
                               Just msg -> do append msg
                                              return $ Just msg
                CommandLine.commandLine get modGuts
        [ ('/' : filename) ] -> do
                gets <- liftIO $ openFile2 filename
                CommandLine.commandLine gets modGuts
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

-- TOFIX: never actually closes
openFile2 :: FilePath -> IO (IO (Maybe String))
openFile2 fileName = do
        h <- openFile fileName ReadMode
        return $ do
                b <- hIsEOF h
                if b then return Nothing
                     else do str <- hGetLine h
                             return (Just $ str ++ "\n")

ppProgram :: ModGuts -> CoreM ModGuts
ppProgram = bindsOnlyPass printBinds

printBinds :: CoreProgram -> CoreM CoreProgram
printBinds binds  = do
  putMsg $ pprCoreBindings binds
  return binds

writeProgram :: FilePath -> ModGuts -> CoreM ModGuts
writeProgram filename =
    bindsOnlyPass (\ binds -> do liftIO $ writeFile filename $ showSDoc $ pprCoreBindings binds
                                 return binds)
