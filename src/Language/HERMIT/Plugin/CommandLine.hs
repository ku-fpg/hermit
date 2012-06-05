{-# LANGUAGE PatternGuards, DataKinds, ScopedTypeVariables #-}

module Language.HERMIT.Plugin.CommandLine (passes) where

import GhcPlugins
import PprCore -- compiler/coreSyn/PprCore.lhs

import System.IO

import Language.HERMIT.Shell.Command as Dispatch
import Language.HERMIT.Plugin.Common
import System.Console.Getline

passes :: [NamedPass]
passes = [("i", logCore "HERMIT.out" interactive)
         ,("h", logCore "HERMIT.out" scripted)
         ]

interactive :: HermitPass
interactive _opts modGuts = do
    elGets <- liftIO getEditor

    let append = appendFile ".hermitlog"
    liftIO $ append "\n-- starting new session\n"
    let get = do str <- elGets "hermit> "
                 maybe (append "-- ^D\n" >> return Nothing)
                       (\m -> append m   >> return (Just m))
                       str

    Dispatch.commandLine get modGuts

scripted :: HermitPass
scripted opts modGuts =
    case opts of
        [ ('/' : filename) ] -> do
            gets <- liftIO $ openFile2 filename
            Dispatch.commandLine gets modGuts
        _ -> return modGuts

logCore :: FilePath -> HermitPass -> HermitPass
logCore filename pass opts modGuts = do
    _ <- writeProgram ("BEFORE." ++ filename) modGuts
    modGuts' <- pass opts modGuts
    writeProgram ("AFTER." ++ filename) modGuts'

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

writeProgram :: FilePath -> ModGuts -> CoreM ModGuts
writeProgram filename =
    bindsOnlyPass (\ binds -> do liftIO $ writeFile filename $ showSDoc $ pprCoreBindings binds
                                 return binds)
