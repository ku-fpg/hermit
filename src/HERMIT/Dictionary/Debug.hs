{-# LANGUAGE FlexibleContexts #-}
module HERMIT.Dictionary.Debug
       ( -- * Debugging Dictionarys
         externals
       , bracketR
       , observeR
       , observeFailureR
       , traceR
       )
where

import Control.Arrow

import HERMIT.Kure
import HERMIT.External
import HERMIT.Monad

-- | Exposed debugging 'External's.
externals :: [External]
externals = map (.+ Debug)
         [ external "trace" (traceR :: String -> RewriteH Core)
                [ "give a side-effect message as output when processing this command" ]
         , external "observe" (observeR :: String -> RewriteH Core)
                [ "give a side-effect message as output, and observe the value being processed" ]
         , external "observe-failure" (observeFailureR :: String -> RewriteH Core -> RewriteH Core)
                [ "give a side-effect message if the rewrite fails, including the failing input" ]
         , external "bracket" (bracketR :: String -> RewriteH Core -> RewriteH Core)
                [ "if given rewrite succeeds, see its input and output" ]
         ]

-- | If the 'Rewrite' fails, print out the 'Core', with a message.
observeFailureR :: Injection a CoreTC => String -> RewriteH a -> RewriteH a
observeFailureR str m = m <+ observeR str

-- | Print out the 'Core', with a message.
observeR :: Injection a CoreTC => String -> RewriteH a
observeR msg = extractR $ sideEffectR $ \ cxt core ->
        sendDebugMessage $ DebugCore msg cxt core

-- | Just say something, every time the rewrite is done.
traceR :: String -> RewriteH a
traceR msg = sideEffectR $ \ _ _ -> sendDebugMessage $ DebugTick msg

-- | Show before and after a rewrite.
bracketR :: Injection a CoreTC => String -> RewriteH a -> RewriteH a
bracketR msg rr = do
    -- Be careful to only run the rr once, in case it has side effects.
    (e,r) <- idR &&& attemptM rr
    either fail (\ e' -> do _ <- return e >>> observeR before
                            return e' >>> observeR after) r
    where before = msg ++ " (before)"
          after  = msg ++ " (after)"
-- attemptM :: MonadCatch m => m a -> m (Either String a)
