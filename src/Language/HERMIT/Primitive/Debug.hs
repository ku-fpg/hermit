{-# LANGUAGE FlexibleContexts, TypeFamilies #-}
module Language.HERMIT.Primitive.Debug
       ( -- * Debugging Primitives
         externals
       , traceR
       , observeR
       , observeFailureR
       )
where

import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.Monad

-- | Exposed debugging 'External's.
externals :: [External]
externals = map (.+ Debug)
         [ external "trace" (traceR :: String -> RewriteH Core)
                [ "give a side-effect message as output when processing this command" ]
         , external "observe" (observeR :: String -> RewriteH Core)
                [ "give a side-effect message as output, and observe the value being processed" ]
         , external "observe-failure" (observeFailureR :: String -> RewriteH Core -> RewriteH Core)
                [ "give a side-effect message if the rewrite fails, including the failing input" ]
         ]

-- | If the 'Rewrite' fails, print out the 'Core', with a message.
observeFailureR :: (Injection a Core, Generic a ~ Core) => String -> RewriteH a -> RewriteH a
observeFailureR str m = m <+ observeR str

-- | Print out the 'Core', with a message.
observeR :: (Injection a Core, Generic a ~ Core) => String -> RewriteH a
observeR msg = extractR $ sideEffectR $ \ cxt core ->
        sendDebugMessage $ DebugCore msg cxt core

-- | Just say something, every time the rewrite is done.
traceR :: String -> RewriteH a
traceR msg = sideEffectR $ \ _ _ -> sendDebugMessage $ DebugTick msg
