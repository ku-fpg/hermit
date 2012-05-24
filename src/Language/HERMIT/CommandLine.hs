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

data CommandLineState = CommandLineState
        { cl_lenses :: [LensH Core Core] -- ^ stack of lenses
        , cl_pretty :: String            -- ^ which pretty printer to use
        , cl_cursor :: AST               -- ^ the current AST
        }

commandLine :: IO (Maybe String) -> ModGuts -> CoreM ModGuts
commandLine gets = hermitKernel $ \ kernel ast -> do
  let dict = dictionary shell_externals

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
                                        dict
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

      act st (Message msg) = putStrLn msg >> loop st

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
