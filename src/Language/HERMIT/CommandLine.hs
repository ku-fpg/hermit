{-# LANGUAGE FlexibleInstances #-}

module Language.HERMIT.CommandLine where

import GhcPlugins

import Data.Char

import Language.HERMIT.HermitExpr
import Language.HERMIT.HermitKure
import Language.HERMIT.Dictionary
import Language.HERMIT.Kernel

commandLine :: IO (Maybe String) -> ModGuts -> CoreM ModGuts
commandLine gets modGuts = runCommands (liftIO getCommand) (liftIO.printKernelOutput) modGuts
  where
    getCommand :: IO KernelCommand
    getCommand = do maybeLine <- gets
                    case maybeLine of
                      Nothing            -> return Exit
                      Just ('-':'-':msg) -> return (Message msg)
                      Just line          -> if all isSpace line
                                             then getCommand
                                             else case parseExprH line of
                                                    Left  msg  -> putStrLn ("parse failure: " ++ msg) >> getCommand
                                                    Right expr -> case interpExprH expr of
                                                                    Left msg  -> putStrLn msg >> getCommand
                                                                    Right cmd -> return cmd

printKernelOutput :: KernelOutput -> IO ()
printKernelOutput (ErrorMsg msg)    = putStrLn msg
printKernelOutput (QueryResult msg) = putStrLn msg
printKernelOutput (FocusChange _ a) = putStrLn (show2 a)
printKernelOutput (CoreChange a)    = putStrLn (show2 a)

-- THIS CODE IS FROM BEFORE THE KernalOutput DATA TYPE
-- commandLine :: IO (Maybe String) -> ModGuts -> CoreM ModGuts
-- commandLine gets modGuts = do
--     let getCmd :: HermitEnv -> Core -> IO Command
--         getCmd _ e = do
--           putStrLn (show2 e)
--           let loop = do
--                 maybeLine <- gets
--                 case maybeLine of
--                    Nothing -> return Exit
--                    Just line | all isSpace line -> loop
--                    Just ('-':'-': _) -> loop       -- comment
--                    Just line -> do
--                      case Expr.parseExpr line of
--                                  Left msg -> do
--                                      putStrLn $ "parse failure: " ++ show msg
--                                      loop
--                                  Right expr -> case interpExpr expr of
--                                                  Right cmd -> return cmd
--                                                  Left msg -> do
--                                                          putStrLn msg
--                                                          loop
--           loop

--     runCommands (liftIO getCmd) print modGuts


-- Later, this will have depth, and other pretty print options.
class Show2 a where
        show2 :: a -> String

instance Show2 Core where
        show2 (ModGutsCore   m)  = show2 m
        show2 (ProgramCore   p)  = show2 p
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
