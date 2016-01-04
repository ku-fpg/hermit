module HERMIT.Win32.Console (isCygwinConsole) where

import Control.Exception (try)
import System.Environment

-- TODO: Figure out a more intelligent way to do this
isCygwinConsole :: IO Bool
isCygwinConsole = do
    result <- try $ getEnv "_" -- Cygwin defines this, Windows Cmd does not
    return $ case (result :: Either IOError String) of
                  Left _ -> False
                  Right _ -> True
