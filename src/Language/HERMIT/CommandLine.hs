{-# LANGUAGE FlexibleInstances, GADTs #-}

module Language.HERMIT.CommandLine where

import GhcPlugins

import Language.KURE

import Data.Char

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.HermitKure
import Language.HERMIT.Dictionary
import Language.HERMIT.Kernel
import qualified Language.HERMIT.Expr as Expr

import Language.HERMIT.Primitive.Inline

commandLine :: IO (Maybe String) -> ModGuts -> CoreM ModGuts
commandLine gets modGuts = runCommands (liftIO getCmd) (liftIO.printKernelOutput) modGuts
  where
    getCmd :: IO KernelCommand
    getCmd = do maybeLine <- gets
                case maybeLine of
                  Nothing            -> return Exit
                  Just ('-':'-':msg) -> return (Message msg)
                  Just line          -> if all isSpace line 
                                         then getCmd
                                         else case Expr.parseExpr line of
                                                Left  msg  -> putStrLn ("parse failure: " ++ msg) >> getCmd
                                                Right expr -> case interpExpr expr of
                                                                Left msg  -> putStrLn msg >> getCmd
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
