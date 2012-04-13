{-# LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleInstances, KindSignatures, GADTs, DataKinds, TypeOperators #-}

-- A Hermitage is a place of quiet reflection.

module Language.HERMIT.CommandLine where

import GhcPlugins

import Data.Char

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.Types
import Language.HERMIT.KURE
import Language.HERMIT.Dictionary
import Language.HERMIT.Command
import qualified Language.HERMIT.Expr as Expr

import Language.HERMIT.Primitive.Inline



commandLine :: IO (Maybe String) -> ModGuts -> CoreM ModGuts
commandLine gets modGuts = do
    let getCmd :: Context Core -> IO Command
        getCmd lh = do
          let (Context _ e) = lh
          putStrLn (show2 e)
          let loop = do
                maybeLine <- gets
                case maybeLine of
                   Nothing -> return PopFocus
                   Just line | all isSpace line -> loop
                   Just ('-':'-': _) -> loop       -- comment
                   Just line -> do
                     case Expr.parseExpr line of
                                 Left msg -> do
                                     putStrLn $ "parse failure: " ++ show msg
                                     loop
                                 Right expr -> case interpExpr expr of
                                                 Right cmd -> return $ cmd
                                                 Left msg -> do
                                                         putStrLn $ msg
                                                         loop
          loop

    runCommands getCmd print modGuts
--    commands el 0 h

{-
--- THIS CODE IS OLD
commands :: forall c a . (Term a, Show2 a, Generic a ~ Core) => EditLine -> Int -> H.Hermitage c a -> CoreM (H.Hermitage c a)
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
                    [nstr] | all isDigit nstr ->
                        focusCommand (focusOnPath [read nstr] :: Rewrite (Generic a) -> Rewrite a)
                    ["*inline"] -> do
                        res <- H.applyRewrite (extractR $ bottomupR $ promoteR $ tryR $ inline) h
                        case res of
                          Left msg -> do
                             liftIO $ print msg
                             commands el n h
                          Right h1 -> do
                             commands el n h1
                    ["focusB",nstr] | all isDigit nstr ->
                        focusCommand (focusOnPath [read nstr] :: Rewrite (Bind Id) -> Rewrite a)
                    ["focusE",nstr] | all isDigit nstr ->
                        focusCommand (focusOnPath [read nstr] :: Rewrite (Expr Id) -> Rewrite a)
                    other -> do
                        liftIO $ putStrLn $ "do not understand " ++ show other
                        commands el n h
  where
    focusCommand :: (Term b, Show2 b, Generic b ~ Core) => (Rewrite b -> Rewrite a) -> CoreM (H.Hermitage c a)
    focusCommand kick =  do
                        res <- H.focusHermitage kick h
                        case res of
                          Left msg -> do
                             liftIO $ print msg
                             commands el n h
                          Right h1 -> do
                             h2 <- commands el (succ n) h1
                             res <- H.unfocusHermitage h2
                             case res of
                               Left msg -> do
                                 liftIO $ print msg
                                 commands el n h
                               Right h3 -> do
                                 commands el n h3

-}

-- Later, this will have depth, and other pretty print options.
class Show2 a where
        show2 :: a -> String

instance Show2 Core where
        show2 (ModGutsCore   m)  = show2 m
        show2 (ProgramCore   p)  =  show2 p
        show2 (BindCore      bd) = show2 bd
        show2 (ExprCore      e)  = show2 e
        show2 (AltCore       a)  = show2 a

instance Show2 ModGuts where
        show2 modGuts =
                "[ModGuts for " ++ showSDoc (ppr (mg_module modGuts)) ++ "]\n" ++
                 show (length (mg_binds modGuts)) ++ " binding group(s)\n" ++
                 show (length (mg_rules modGuts)) ++ " rule(s)\n"

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
