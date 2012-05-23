{-# LANGUAGE FlexibleInstances #-}

module Language.HERMIT.CommandLine where

import GhcPlugins

import Data.Char
import Control.Applicative

import qualified Data.Map as M
import qualified Text.PrettyPrint.MarkedHughesPJ as PP

import Language.HERMIT.HermitExpr
import Language.HERMIT.HermitKure
import Language.HERMIT.Dictionary
import Language.HERMIT.Kernel
import Language.HERMIT.PrettyPrinter

import Language.KURE.Translate

data CommandLineState = CommandLineState
        { cl_lenses :: [LensH Core Core] -- ^ stack of lenses
        , cl_pretty :: String            -- ^ which pretty printer to use
        , cl_cursor :: AST               -- ^ the current AST
        }

commandLine :: IO (Maybe String) -> ModGuts -> CoreM ModGuts
commandLine gets = hermitKernel $ \ kernel ast -> do
  let quit = quitK kernel
  let query = queryK kernel

  let pretty :: CommandLineState -> PrettyH Core
      pretty st = case M.lookup (cl_pretty st) pp_dictionary of
                   Just pp -> pp
                   Nothing -> pure (PP.text "<<pretty>>")

  let myLens st = case cl_lenses st of
                    [] -> idL
                    (ls:_) -> ls

  let loop :: CommandLineState -> IO ()
      loop st = do
          print (length (cl_lenses st), cl_pretty st,cl_cursor st)

          maybeLine <- gets
          case maybeLine of
            Nothing            -> act st Exit
            Just ('-':'-':msg) -> loop st
            Just line          ->
                if all isSpace line
                then loop st
                else case parseExprH line of
                       Left  msg  -> putStrLn ("parse failure: " ++ msg) >> loop st
                       Right expr -> case interpExprH expr of
                                       Left msg  -> putStrLn msg >> loop st
                                       Right cmd -> act st cmd

      act st Exit   = quit (cl_cursor st)
      act st (PushFocus ls) = do
              let newlens = myLens st `composeL` ls
              doc <- query ast (translateL newlens >-> (pretty st))
              print doc
              loop (st { cl_lenses = newlens : cl_lenses st })
      act st PopFocus = do
              let st' = st { cl_lenses = case cl_lenses st of
                                          [] -> []
                                          (_:xs) -> xs
                           }
              -- something changed, to print
              doc <- query ast (focusT (myLens st') (pretty st))
              print doc
              loop st'
      act st SuperPopFocus = do
              let st' = st { cl_lenses = []
                           }
              -- something changed, to print
              doc <- query ast (focusT (myLens st')  (pretty st))
              print doc
              loop st'
      act st (Query q) = do

              -- something changed, to print
              doc <- query ast (focusT (myLens st) q)
              print doc
              -- same state
              loop st

      act st (Apply rr) = do
              -- something changed (you've applied)
              ast' <- applyK kernel ast (focusR (myLens st) rr)
              doc  <- query ast' (focusT (myLens st) (pretty st))
              print doc
              -- same state
              loop (st { cl_cursor = ast' })

  -- recurse using the command line
  loop $ CommandLineState [] "ghc" ast

  -- we're done
  quitK kernel ast
  return ()

focusR = rewriteL

focusT :: (Monad m) => Lens c m a b -> Translate c m b d -> Translate c m a d
focusT lens trans = lens >-> translate (\ _ ((c,b),_) -> apply trans c b)


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

