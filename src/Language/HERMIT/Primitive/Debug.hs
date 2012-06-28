{-# LANGUAGE FlexibleContexts, TypeFamilies #-}
module Language.HERMIT.Primitive.Debug where

import GhcPlugins as GHC

import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.PrettyPrinter

externals :: [External]
externals =
         [ external "trace" (traceR :: String -> RewriteH Core)
                [ "give a side-effect message as output when processing this command" ]
         , external "observe" (observeR :: String -> RewriteH Core)
                [ "give a side-effect message as output, and observe the value being processed" ]
         , external "observe-failure" (observeFailureR :: String -> RewriteH Core -> RewriteH Core)
                [ "give a side-effect message if the rewrite fails, including the failing input" ]
         ]

observeFailureR :: (Injection a Core, Generic a ~ Core) => String -> RewriteH a -> RewriteH a
observeFailureR str m = m <+ observeR str

-- Print out the Core, with a message
observeR :: (Injection a Core, Generic a ~ Core) => String -> RewriteH a
observeR msg = extractR $ sideEffectR $ \ _ core -> do
        liftIO (putStrLn $ "[traceR: " ++ msg ++ "]")
        liftIO (putStrLn $ show2 (core :: Core))
        liftIO (putStrLn $ "[end traceR]")

-- Just say something, every time the rewrite is done
traceR :: String -> RewriteH a
traceR msg = sideEffectR $ \ _ _ -> liftIO (putStrLn $ "traceR: " ++ msg)
