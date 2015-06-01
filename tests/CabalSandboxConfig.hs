-- Due to a cabal-install bug, the CABAL_SANDBOX_CONFIG environment variable is not
-- loaded when cabal test is run, so we resort to calling
--
--     cabal exec runhaskell CabalSandboxConfig.hs
--
-- to infer what CABAL_SANDBOX_CONFIG is during cabal test.
module Main (main) where

import Control.Exception (try)
import System.Environment (getEnv)

main :: IO ()
main = do
    mbSandboxCfg <- try $ getEnv "CABAL_SANDBOX_CONFIG"
    putStr $ case (mbSandboxCfg :: Either IOError FilePath) of
        Left  _  -> ""
        Right fp -> "--sandbox-config-file=" ++ fp
