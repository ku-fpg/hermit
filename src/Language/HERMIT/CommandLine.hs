{-# LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleInstances, KindSignatures, GADTs #-}

-- A Hermitage is a place of quiet reflection.

module Language.HERMIT.CommandLine where

import GhcPlugins

import System.Console.Editline

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.Types
import Language.HERMIT.Hermitage

commandLine :: Hermitage () ModGuts -> CoreM (Hermitage () ModGuts)
commandLine h = do
    el <- liftIO $ elInit "hermit"
    liftIO $ setEditor el Emacs
    commands el 0 h

-- The arguments here should be bundled into a datastructure.
-- (except the Hermitage c a, because the polymorphism here would stop simple updates.)

commands :: forall c a . (Term a, Show2 a) => EditLine -> Int -> Hermitage c a -> CoreM (Hermitage c a)
commands el n h = do
         liftIO $ setPrompt el (return $ show n ++ "> ")
         maybeLine <- liftIO $ elGets el
         case maybeLine of
             Nothing ->
                do liftIO $ print "ctrl-D"
                   return h
--             return h -- ctrl-D
             Just line -> do
                 let line' = init line -- remove trailing '\n'
                 liftIO $ putStrLn $ "User input: " ++ show line'
                 case words line' of
                    ["?"] -> do
                        a <- getForeground h
                        liftIO $ putStrLn "Foreground: "
                        liftIO $ putStrLn (show2 a)
                        commands el n h
                    ["focus"] -> do
                        res <- focusHermitage (focusOnBinding) h
                        case res of
                           Left msg -> do
                             liftIO $ print msg
                             commands el n h
                           Right h1 -> do
                             commands el (succ n) h1
                             let h2 = unfocusHermitage h1
                             commands el n h2
                    other -> do
                        liftIO $ putStrLn $ "do not understand " ++ show other
                        commands el n h

--         interp

-- Later, this will have depth, and other pretty print options.
class Show2 a where
        show2 :: a -> String

instance Show2 ModGuts where
        show2 _ = "ModGuts"

instance Show2 (Expr Id) where
        show2 _ = "ModGuts"

instance Show2 (Bind Id) where
        show2 _ = "ModGuts"
