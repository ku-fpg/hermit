{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
module HERMIT.Dictionary.Debug
    ( -- * Debugging Rewrites
      externals
    , bracketR
    , observeR
    , observeFailureR
    , traceR
    ) where

import Control.Arrow

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.Kure
import HERMIT.Monad

import HERMIT.Exception

import Control.Exception hiding (catch)

-- | Exposed debugging 'External's.
externals :: [External]
externals = map (.+ Debug)
    [ external "trace" (traceR :: String -> RewriteH LCoreTC)
        [ "give a side-effect message as output when processing this command" ]
    , external "observe" (observeR :: String -> RewriteH LCoreTC)
        [ "give a side-effect message as output, and observe the value being processed" ]
    , external "observe-failure" (observeFailureR :: String -> RewriteH LCoreTC -> RewriteH LCoreTC)
        [ "give a side-effect message if the rewrite fails, including the failing input" ]
    , external "bracket" (bracketR :: String -> RewriteH LCoreTC -> RewriteH LCoreTC)
        [ "if given rewrite succeeds, see its input and output" ]
    ]

-- | If the 'Rewrite' fails, print out the 'Core', with a message.
observeFailureR :: ( Injection a LCoreTC, LemmaContext c, ReadBindings c, ReadPath c Crumb
                   , HasHermitMEnv m, HasLemmas m, LiftCoreM m, MonadCatch m )
                => String -> Rewrite c m a -> Rewrite c m a
observeFailureR str m = m <+ observeR str

-- | Print out the 'Core', with a message.
observeR :: ( MonadThrow m, Injection a LCoreTC, LemmaContext c, ReadBindings c, ReadPath c Crumb
            , HasHermitMEnv m, HasLemmas m, LiftCoreM m )
         => String -> Rewrite c m a
observeR msg = extractR $ sideEffectR $ \ cxt -> sendKEnvMessage . DebugCore msg cxt

-- | Just say something, every time the rewrite is done.
traceR :: (HasHermitMEnv m, HasLemmas m, LiftCoreM m) => String -> Rewrite c m a
traceR msg = sideEffectR $ \ _ _ -> sendKEnvMessage $ DebugTick msg

-- | Show before and after a rewrite.
bracketR :: ( Injection a LCoreTC, LemmaContext c, ReadBindings c, ReadPath c Crumb
            , HasHermitMEnv m, HasLemmas m, LiftCoreM m, MonadCatch m )
         => String -> Rewrite c m a -> Rewrite c m a
bracketR msg rr = do
    -- Be careful to only run the rr once, in case it has side effects.
    (e,r) <- idR &&& (attemptM rr :: _ (Either SomeException _))
    either fail (\ e' -> do _ <- return e >>> observeR before
                            return e' >>> observeR after) (left show r)
    where before = msg ++ " (before)"
          after  = msg ++ " (after)"
