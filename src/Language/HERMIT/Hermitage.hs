-- A Hermitage is a place of quiet reflection.

module Language.HERMIT.Hermitage where

import GhcPlugins

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.Types

-- abstact outside this module
data Hermitage a = Hermiage
--        { close :: IO () }


-- Create a new Hermitage, does not return until the interaction
-- is completed. It is thread safe (any thread can call a 'Hermitage' function),
-- but not after the callback has terminated and returned.
new :: (Hermitage ModGuts -> IO (Hermitage ModGuts)) -> ModGuts -> CoreM ModGuts
new k modGuts = return modGuts

-- Some of these do not need to be in IO,
-- but there are plans for async-access, memoization, etc,
-- so we'll stick them in the monad right now.

-- | What are the current module guts?
getModGuts :: Hermitage a -> IO ModGuts
getModGuts = undefined

getForeground :: Hermitage a -> IO a
getForeground = undefined
-- | getBackground gets the background of the Hermitage,
-- getBackground

applyRewrite :: Rewrite a -> Hermitage a -> IO (Hermitage a)
applyRewrite = undefined
