{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, GADTs, KindSignatures, TypeFamilies, DeriveDataTypeable #-}

module Language.HERMIT.CommandLine where

import GhcPlugins

import Data.Char
import Control.Applicative
import Data.Monoid
import Control.Exception.Base
import Data.Dynamic

import qualified Data.Map as M
import qualified Text.PrettyPrint.MarkedHughesPJ as PP

import Language.HERMIT.HermitExpr
import Language.HERMIT.HermitKure
import Language.HERMIT.Kernel
import Language.HERMIT.Dictionary
import Language.HERMIT.Kernel
import Language.HERMIT.PrettyPrinter
import Language.HERMIT.Interp
import Language.HERMIT.Shell.Command

import Language.KURE

import Language.HERMIT.External
{-
data ShellCommand :: * where
   Status        ::                             ShellCommand
   Message       :: String                   -> ShellCommand
   PushFocus     :: LensH Core Core          -> ShellCommand
   PopFocus      ::                             ShellCommand
   SuperPopFocus ::                             ShellCommand
   KernelCommand :: KernelCommand            -> ShellCommand

data ShellCommandBox = ShellCommandBox ShellCommand deriving Typeable

instance Extern ShellCommand where
    type Box ShellCommand = ShellCommandBox
    box i = ShellCommandBox i
    unbox (ShellCommandBox i) = i


interpShellCommand :: [Interp ShellCommand]
interpShellCommand =
                [ Interp $ \ (ShellCommandBox cmd)       -> cmd
                , Interp $ \ (LensCoreCoreBox l)         -> PushFocus l
                , Interp $ \ (IntBox i)                  -> PushFocus $ childL i
                , Interp $ \ (StringBox str)             -> Message str
                ]

shell_externals :: [External]
shell_externals =
   [
-- TODO: restore Exit
--     external "exit"            Exit
--       [ "exits HERMIT" ]
     external "status"          Status
       [ "redisplays current state" ]
   , external "pop"             PopFocus
       [ "pops one lens" ]
   , external "."               PopFocus
       [ "pops one lens" ]
   , external "superpop"        SuperPopFocus
       [ "pops all lenses" ]
   ]

-}
data CommandLineState = CommandLineState
        { cl_lenses :: [LensH Core Core] -- ^ stack of lenses
        , cl_pretty :: String            -- ^ which pretty printer to use
        , cl_cursor :: AST               -- ^ the current AST
        }

commandLine :: IO (Maybe String) -> ModGuts -> CoreM ModGuts
commandLine gets = hermitKernel $ \ kernel ast -> do
  let quit = quitK kernel
  let query :: AST -> TranslateH Core a -> IO a
      query = queryK kernel

  let catch :: IO a -> (String -> IO a) -> IO a
      catch = catchJust (\ (err :: IOException) -> return (show err))

  let pretty :: CommandLineState -> PrettyH Core
      pretty st = case M.lookup (cl_pretty st) pp_dictionary of
                   Just pp -> pp
                   Nothing -> pure (PP.text "<<pretty>>")

  let myLens st = case cl_lenses st of
                    [] -> idL
                    (ls:_) -> ls

  let showFocus st = (do
        doc <- query (cl_cursor st) (focusT (myLens st) (pretty st))
        print doc
        return True) `catch` \ msg -> do
                        putStrLn $ "Error thrown: " ++ msg
                        return False

  let loop :: CommandLineState -> IO ()
      loop st = do
          print (length (cl_lenses st), cl_pretty st,cl_cursor st)

          maybeLine <- gets
          case maybeLine of
            Nothing            -> kernelAct st Exit
            Just ('-':'-':msg) -> loop st
            Just line          ->
                if all isSpace line
                then loop st
                else case parseExprH line of
                       Left  msg  -> putStrLn ("parse failure: " ++ msg) >> loop st
                       Right expr ->
                           case interpExprH
                                        (toDictionary shell_externals)
                                        (interpShellCommand
                                           ++  map (fmap KernelCommand) interpKernelCommand)
                                        expr of
                            Left msg  -> putStrLn msg >> loop st
                            Right cmd -> act st cmd


      act st Status = do
              True <- showFocus st
              loop st

      act st (PushFocus ls) = do
              let newlens = myLens st `composeL` ls
              let st' = st { cl_lenses = newlens : cl_lenses st }
              good <- showFocus st'
              if good then loop st'
                      else loop st
      act st PopFocus = do
              let st' = st { cl_lenses = case cl_lenses st of
                                          [] -> []
                                          (_:xs) -> xs
                           }
              -- something changed, to print
              True <- showFocus st'
              loop st'
      act st SuperPopFocus = do
              let st' = st { cl_lenses = []
                           }
              -- something changed, to print
              True <- showFocus st'
              loop st'

      act st (KernelCommand cmd) = kernelAct st cmd

      kernelAct st Exit   = quit (cl_cursor st)

      kernelAct st (Query q) = do

              -- something changed, to print
              (do doc <- query ast (focusT (myLens st) q)
                  print doc) `catch` \ msg -> putStrLn $ "Error thrown: " ++ msg
              -- same state
              loop st

      kernelAct st (Apply rr) = do
              -- something changed (you've applied)
              st2 <- (do ast' <- applyK kernel ast (focusR (myLens st) rr)
                         let st' = st { cl_cursor = ast' }
                         showFocus st'
                         return st') `catch` \  msg -> do
                                        putStrLn $ "Error thrown: " ++ msg
                                        return st
              loop st2

  -- recurse using the command line
  loop $ CommandLineState [] "ghc" ast

  -- we're done
  quitK kernel ast
  return ()

{-
{-
   Exit          ::                             KernelCommand
   Status        ::                             KernelCommand
   Message       :: String                   -> KernelCommand
   Apply         :: RewriteH Core            -> KernelCommand
-}

{-
        runCommands (liftIO getCommand) (liftIO.printKernelOutput) modGuts
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
-}


commandLine2 :: IO (Maybe String) -> ModGuts -> CoreM ModGuts
commandLine2 gets modGuts = runCommands (liftIO getCommand) (liftIO.printKernelOutput) modGuts
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

-}