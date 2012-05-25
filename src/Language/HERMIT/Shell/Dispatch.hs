{-# LANGUAGE FlexibleInstances, ScopedTypeVariables, GADTs, KindSignatures, TypeFamilies, DeriveDataTypeable #-}

module Language.HERMIT.Shell.Dispatch where

import Prelude hiding (catch)

import GhcPlugins hiding (L)

import Data.Char
import Control.Applicative
import Data.List (intercalate)
import Control.Exception.Base hiding (catch)

import qualified Data.Map as M
import qualified Text.PrettyPrint.MarkedHughesPJ as PP
import System.Console.ANSI

import Language.HERMIT.HermitExpr
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitKure
import Language.HERMIT.Dictionary
import Language.HERMIT.Kernel
import Language.HERMIT.PrettyPrinter
import Language.HERMIT.Interp
import Language.HERMIT.Shell.Command

import Language.KURE

data CommandLineState = CommandLineState
        { cl_lens   :: LensH Core Core  -- ^ stack of lenses
        , cl_pretty :: String           -- ^ which pretty printer to use
        , cl_cursor :: AST              -- ^ the current AST
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

  let showFocus :: CommandLineState -> IO Bool
      showFocus st = (do
        doc <- query (cl_cursor st) (focusT (cl_lens st) (pretty st))
        renderShellDoc doc
        return True) `catch` \ msg -> do
                        putStrLn $ "Error thrown: " ++ msg
                        return False

  let loop :: CommandLineState -> IO ()
      loop st = do
          print (cl_pretty st,cl_cursor st)

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

      showFocusLoop :: CommandLineState -> IO ()
      showFocusLoop st = whenM (showFocus st) (loop st)

      act :: CommandLineState -> ShellCommand -> IO ()
      act st Status = do
--              True <- showFocus st
              print "starting"
              ContextPath doc <- query (cl_cursor st) (focusT (cl_lens st) pathT)
              print (reverse doc)
              loop st
      act st (PushFocus ls) = do
              let new_lens = cl_lens st `composeL` ls
              -- below is a common ending
              condM (query (cl_cursor st) (testA new_lens))
                    (showFocusLoop st)
                    (showFocusLoop $ st {cl_lens = new_lens})
      act st (Direction dir) = do
              ContextPath c_path      <- query (cl_cursor st) (focusT (cl_lens st) pathT)
              child_count <- query (cl_cursor st) (focusT (cl_lens st) (liftT numChildren))
              print (c_path,child_count,dir)
              let new_lens = case (dir, c_path) of
                       (U, _ : rest)              -> pathL $ reverse rest
                       (D, _)                     -> pathL $ reverse (0 : c_path)
                       (R, kid : rest)            -> pathL $ reverse ((kid + 1) : rest)
                       (L, kid : rest)  | kid > 0 -> pathL $ reverse ((kid - 1) : rest)
                       _               -> cl_lens st
              -- TODO: fix to ring bell if stuck
              -- something changed, to print
              condM (query (cl_cursor st) (testA new_lens))
                    (showFocusLoop st) -- bell (still print for now)
                    (showFocusLoop $ st {cl_lens = new_lens})
      act st SuperPopFocus = showFocusLoop $ st {cl_lens = idL} -- something changed, to print

      act st (Message msg) = putStrLn msg >> loop st

      act st (SetPretty pp) = do
              st' <- maybe (do putStrLn $ "List of Pretty Printers: " ++ intercalate ", " (M.keys pp_dictionary)
                               return st)
                           (const $ return $ st { cl_pretty = pp })
                           (M.lookup pp pp_dictionary)
              loop st'

      act st (KernelCommand cmd) = kernelAct st cmd

      kernelAct st Exit   = quit (cl_cursor st)

      kernelAct st (Query q) = do

              -- something changed, to print
              (query (cl_cursor st) (focusT (cl_lens st) q) >>= print)
                `catch` \ msg -> putStrLn $ "Error thrown: " ++ msg
              -- same state
              loop st

      kernelAct st (Apply rr) = do
              -- something changed (you've applied)
              st2 <- (do ast' <- applyK kernel (cl_cursor st) (focusR (cl_lens st) rr)
                         let st' = st { cl_cursor = ast' }
                         showFocus st'
                         return st') `catch` \  msg -> do
                                        putStrLn $ "Error thrown: " ++ msg
                                        return st
              loop st2

  -- recurse using the command line
  loop $ CommandLineState idL "ghc" ast

  -- we're done
  quitK kernel ast
  return ()


-- Here is our render for the pretty printing output

renderShellDoc :: DocH -> IO ()
renderShellDoc doc = PP.fullRender PP.PageMode 80 1 marker (\ _ -> putStrLn "") doc [Nothing]
  where   -- color = Nothing means set back to terminal default
          marker :: PP.TextDetails HermitMark -> ([Maybe Color] -> IO ()) -> ([Maybe Color]-> IO ())
          marker m rest cols = case m of
                  PP.Chr ch   -> putChar ch >> rest cols
                  PP.Str str  -> putStr str >> rest cols
                  PP.PStr str -> putStr str >> rest cols

                  PP.Mark (PushAttr (Color c)) -> do
                        let col = case c of
                                    VarColor     -> Blue
                                    SyntaxColor  -> Green
                                    KeywordColor -> Magenta
                        setSGR [ SetColor Foreground Dull col ]
                        rest (Just col : cols)
                  PP.Mark (PopAttr) -> do
                        let (_:cols') = cols
                        setSGR [maybe Reset (SetColor Foreground Dull) (head cols')]
                        rest cols'

