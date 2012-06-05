{-# LANGUAGE PatternGuards, DataKinds, ScopedTypeVariables #-}

module Language.HERMIT.Plugin.Interactive (plugin) where

import GhcPlugins

import Language.HERMIT.Shell.Command as Dispatch
import Language.HERMIT.Plugin
import System.Console.Getline

plugin :: Plugin
plugin = hermitPlugin interactive

interactive :: HermitPass
interactive _opts modGuts = do
    elGets <- liftIO getEditor

    let append = appendFile ".hermitlog"
    liftIO $ append "\n-- starting new session\n"
    let get = do str <- elGets "hermit> "
                 maybe (append "-- ^D\n" >> return Nothing)
                       (\m -> append m   >> return (Just m))
                       str

    Dispatch.commandLine get modGuts
