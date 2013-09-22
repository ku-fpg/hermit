{-# LANGUAGE TemplateHaskell #-}
module SecondDemo (plugin) where

import Control.Monad

import HERMIT.GHC hiding (display)
import HERMIT.Kure
import HERMIT.Optimize
import HERMIT.Plugin
import HERMIT.Dictionary

import Language.Haskell.TH as TH

plugin = optimize $ \ opts -> do
    forM_ opts $ \ o -> do
        at (bindingOfT $ cmpTHName2Var $ TH.mkName o) display
    left <- liftM phasesLeft getPhaseInfo
    when (notNull left) $ liftIO $ putStrLn $ "=========== " ++ show (head left) ++ " ==========="
