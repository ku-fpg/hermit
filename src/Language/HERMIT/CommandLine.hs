{-# LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleInstances, KindSignatures, GADTs, DataKinds, TypeOperators #-}

-- A Hermitage is a place of quiet reflection.

module Language.HERMIT.CommandLine where

import GhcPlugins

import System.Console.Editline
import Data.Char

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.Types
import qualified Language.HERMIT.Hermitage as H
import Language.HERMIT.Focus
import Language.HERMIT.KURE

commandLine :: H.Hermitage H.Everything ModGuts -> CoreM (H.Hermitage H.Everything ModGuts)
commandLine h = do
    el <- liftIO $ elInit "hermit"
    liftIO $ setEditor el Emacs
    commands el 0 h

-- The arguments here should be bundled into a datastructure.
-- (except the Hermitage c a, because the polymorphism here would stop simple updates.)

commands :: forall c a . (Term a, Show2 a, Generic a ~ Blob) => EditLine -> Int -> H.Hermitage c a -> CoreM (H.Hermitage c a)
commands el n h = do
         let (Context _ e) = H.getForeground h
--         liftIO $ putStrLn "Foreground: "
         liftIO $ putStrLn (show2 e)
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
                        let (Context _ e) = H.getForeground h
                        liftIO $ putStrLn "Foreground: "
                        liftIO $ putStrLn (show2 e)
                        commands el n h
                    ["focus",nstr] | all isDigit nstr ->
                        focusCommand (focusOnPath [read nstr] :: Rewrite (Generic a) -> Rewrite a)
                    ["focusP",nstr] | all isDigit nstr ->
                        focusCommand (focusOnPath [read nstr] :: Rewrite CoreProgram -> Rewrite a)
                    ["focusB",nstr] | all isDigit nstr ->
                        focusCommand (focusOnPath [read nstr] :: Rewrite (Bind Id) -> Rewrite a)
                    ["focusE",nstr] | all isDigit nstr ->
                        focusCommand (focusOnPath [read nstr] :: Rewrite (Expr Id) -> Rewrite a)
                    other -> do
                        liftIO $ putStrLn $ "do not understand " ++ show other
                        commands el n h
  where
    focusCommand :: (Term b, Show2 b, Generic b ~ Blob) => (Rewrite b -> Rewrite a) -> CoreM (H.Hermitage c a)
    focusCommand kick =  do
                        res <- H.focusHermitage kick h
                        case res of
                          Left msg -> do
                             liftIO $ print msg
                             commands el n h
                          Right h1 -> do
                             commands el (succ n) h1
                             res <- H.unfocusHermitage h1
                             case res of
                               Left msg -> do
                                 liftIO $ print msg
                                 commands el n h
                               Right h2 -> do
                                 commands el n h2


-- Later, this will have depth, and other pretty print options.
class Show2 a where
        show2 :: a -> String

instance Show2 Blob where
        show2 (ModGutsBlob   m)  = show2 m
        show2 (ProgramBlob   p)  =  show2 p
        show2 (BindBlob      bd) = show2 bd
        show2 (ExprBlob      e)  = show2 e
        show2 (AltBlob       a)  = show2 a

instance Show2 ModGuts where
        show2 modGuts =
                "[ModGuts for " ++ showSDoc (ppr (mg_module modGuts)) ++ "]\n" ++
                 show (length (mg_binds modGuts)) ++ " binding group(s)"

instance Show2 CoreProgram where
        show2 codeProg =
                "[Code Program]\n" ++
                showSDoc (ppr codeProg)

instance Show2 (Expr Id) where
        show2 expr =
                "[Expr]\n" ++
                showSDoc (ppr expr)

instance Show2 (Alt Id) where
        show2 alt =
                "[alt]\n" ++
                showSDoc (ppr alt)


instance Show2 (Bind Id) where
        show2 bind =
                "[Bind]\n" ++
                showSDoc (ppr bind)
