{-# LANGUAGE TemplateHaskell #-}
module SecondDemo (plugin) where

import Control.Monad

import HERMIT.Core
import HERMIT.GHC hiding (display)
import HERMIT.Kure
import HERMIT.Optimize
import HERMIT.Plugin
import HERMIT.Dictionary

import HERMIT.PrettyPrinter.Common
import HERMIT.Shell.Types

import Language.Haskell.TH as TH

plugin = optimize $ \ opts -> do
    modifyCLS $ \ st -> st { cl_pretty_opts = updateTypeShowOption Show (cl_pretty_opts st) }
    at (return $ pathToSnocPath [ModGuts_Prog]) display
    left <- liftM passesLeft getPassInfo
    when (notNull left) $ liftIO $ putStrLn $ "=========== " ++ show (head left) ++ " ==========="
    lastPass $ interactive [] opts
