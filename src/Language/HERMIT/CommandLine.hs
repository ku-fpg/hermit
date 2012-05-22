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

-- Later, this will have depth, and other pretty print options.
class Show2 a where
        show2 :: a -> String

instance Show2 Core where
        show2 (ModGutsCore   m)  = show2 m
        show2 (ProgramCore   p)  = show2 p
        show2 (BindCore      bd) = show2 bd
        show2 (ExprCore      e)  = show2 e
        show2 (AltCore       a)  = show2 a
        show2 (DefCore       a)  = show2 a

instance Show2 ModGuts where
        show2 modGuts =
                "[ModGuts for " ++ showSDoc (ppr (mg_module modGuts)) ++ "]\n" ++
                 show (length (mg_binds modGuts)) ++ " binding group(s)\n" ++
                 show (length (mg_rules modGuts)) ++ " rule(s)\n"

instance Show2 CoreProgram where
        show2 codeProg =
                "[Code Program]\n" ++
                showSDoc (ppr codeProg)

instance Show2 CoreExpr where
        show2 expr =
                "[Expr]\n" ++
                showSDoc (ppr expr)

instance Show2 CoreAlt where
        show2 alt =
                "[alt]\n" ++
                showSDoc (ppr alt)


instance Show2 CoreBind where
        show2 bind =
                "[Bind]\n" ++
                showSDoc (ppr bind)

instance Show2 CoreDef where
        show2 (Def v e) =
                "[Def]\n" ++
                showSDoc (ppr v) ++ " = " ++ showSDoc (ppr e)