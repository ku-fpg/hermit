{-# LANGUAGE PatternGuards, DataKinds, ScopedTypeVariables #-}

module Language.HERMIT.Plugin.Script (plugin) where

import GhcPlugins

import System.IO

import Language.HERMIT.Shell.Command as Dispatch
import Language.HERMIT.Plugin

plugin :: Plugin
plugin = hermitPlugin scripted

scripted :: HermitPass
scripted opts modGuts =
    case opts of
        [ ('/' : filename) ] -> do
            gets <- liftIO $ openFile2 filename
            Dispatch.commandLine gets modGuts
        _ -> return modGuts

-- TOFIX: never actually closes
openFile2 :: FilePath -> IO (IO (Maybe String))
openFile2 fileName = do
        h <- openFile fileName ReadMode
        return $ do
                b <- hIsEOF h
                if b then return Nothing
                     else do str <- hGetLine h
                             return (Just $ str ++ "\n")
