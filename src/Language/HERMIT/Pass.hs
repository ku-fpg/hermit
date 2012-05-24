{-# LANGUAGE PatternGuards, DataKinds, ScopedTypeVariables #-}

module Language.HERMIT.Pass (hermitPass, ppProgram, writeProgram) where

import GhcPlugins
import PprCore -- compiler/coreSyn/PprCore.lhs

--import System.Console.Editline

import Data.List
import Control.Monad
import System.IO

-- The Prelude version of catch has been deprecated.
import Prelude hiding (catch)
import Control.Exception (catch, SomeException)

import Language.HERMIT.Shell.Dispatch as CommandLine


-- Syntax:
--   FullModuleName(filename),    <-- reads Module.hermit
--   FullModuleName(-)            <-- starts the interpreter

hermitPass :: [String] -> ModGuts -> CoreM ModGuts
-- run the command-line option
hermitPass nms modGuts = case candidates of
        [ ('/' : '-': []) ] -> do
                -- Command Line Interp (via the readline API)
{-
                el <- liftIO $ elInit "hermit"
                liftIO $ setEditor el Emacs
                liftIO $ setPrompt el (return "hermit> ")
-}
                let myGetLine :: IO String
                    myGetLine = do
                            hSetBuffering stdin NoBuffering
                            hSetEcho stdin False
                            fn []
                       where
                           fn ('\n':xs) = return (reverse xs)
                           fn xs = do
                                 c <- getChar
                                 fn' c xs

                           fn' c "[\ESC" = do
                                   putChar 'K'
                                   hFlush stdout
                                   return ("esc-" ++ [c])
                           fn' '\DEL' [] = fn []
                           fn' '\DEL' xs = do
                                 putStr "\ESC[D \ESC[D"
                                 hFlush stdout
                                 fn (tail xs)
                           fn' c xs = do
--                                 print (c,xs)
                                 putChar c
                                 hFlush stdout
                                 fn (c : xs)
--                           fn' ('\DEL') [] =


                let elGets :: IO (Maybe String)
                    elGets = do putStr "hermit> "
                                hFlush stdout
                            --    Wouldn't this be simpler?  Or can the string actually be "\EOT"?
                            --    liftM Just getLine `catch` (\ (_ :: SomeException) -> return Nothing)
                                str <- myGetLine `catch` (\ (_ :: SomeException) -> return "\EOT")
                                return $ case str of
                                           "\EOT" -> Nothing
                                           _      -> Just str
                let append = appendFile ".hermitlog"
                liftIO $ append "\n-- starting new session\n"
                let get = do str <- elGets
                             case str of
                               Nothing -> do append "-- ^D\n"
                                             return Nothing
                               Just msg -> do append msg
                                              return $ Just msg
                CommandLine.commandLine get modGuts
        [ ('/' : filename) ] -> do
                gets <- liftIO $ openFile2 filename
                CommandLine.commandLine gets modGuts
        _ -> return modGuts
   where
           modName = showSDoc (ppr (mg_module modGuts))
           candidates = [ drop (length modName) nm
                        | nm <- nms
                        , modName `isPrefixOf` nm
                        ]
{-        --
-- find a function, interprete it (TODO)
hermitPass ['@':nm]  h    = return h
-- Need better error message here
hermitPass other        h = error $ "hermitPass failed" ++ show other
-}

-- TOFIX: never actually closes
openFile2 :: FilePath -> IO (IO (Maybe String))
openFile2 fileName = do
        h <- openFile fileName ReadMode
        return $ do
                b <- hIsEOF h
                if b then return Nothing
                     else do str <- hGetLine h
                             return (Just $ str ++ "\n")

ppProgram :: ModGuts -> CoreM ModGuts
ppProgram = bindsOnlyPass printBinds

printBinds :: CoreProgram -> CoreM CoreProgram
printBinds binds  = do
  putMsg $ pprCoreBindings binds
  return binds

writeProgram :: FilePath -> ModGuts -> CoreM ModGuts
writeProgram filename =
    bindsOnlyPass (\ binds -> do liftIO $ writeFile filename $ showSDoc $ pprCoreBindings binds
                                 return binds)
