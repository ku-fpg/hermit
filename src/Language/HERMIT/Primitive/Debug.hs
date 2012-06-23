{-# LANGUAGE FlexibleContexts #-}
module Language.HERMIT.Primitive.Debug where

import GhcPlugins as GHC

import Language.HERMIT.HermitKure
import Language.HERMIT.External
import Language.HERMIT.PrettyPrinter

externals :: [External]
externals =
         [ external "trace" (traceR :: String -> RewriteH Core)
                [ "give a side-effect message as output when processing this command" ]
--         , external "observe" (observeR :: String -> RewriteH Core)
--                [ "give a side-effect message as output, and observe the value being processed" ]
         ]



-- Print out the Core, with a message
observeR :: (Injection a Core) => String -> RewriteH a
observeR msg = extractR $ sideEffectR $ \ _ core -> do
        liftIO (putStrLn $ "[traceR: " ++ msg ++ "]")
        liftIO (putStrLn $ show2 (core :: Core))
        liftIO (putStrLn $ "[end traceR]")

-- Just say something, every time the rewrite is done
traceR :: String -> RewriteH a
traceR msg = sideEffectR $ \ _ _ -> liftIO (putStrLn $ "traceR: " ++ msg)
