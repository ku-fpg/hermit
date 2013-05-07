{-# LANGUAGE KindSignatures, GADTs #-}
module Language.HERMIT.Optimize
    ( -- * The HERMIT Plugin
      optimize
      -- ** Running translations
    , query
    , run
      -- ** Using the shell
    , interactive
      -- ** Target modifiers
    , at
    , phase
    , allPhases
    ) where

import GhcPlugins hiding (Target, singleton)

import Control.Monad.Operational
import Control.Monad.IO.Class

import Data.Default

import Language.HERMIT.Core
import Language.HERMIT.External hiding (Query, Shell)
import Language.HERMIT.Kernel.Scoped
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.Plugin
import qualified Language.HERMIT.Shell.Command as Shell

import System.Console.Haskeline (defaultBehavior)

data Target = Target { atPhase :: Maybe (Either Int CorePass) {- phase which its after -}
                     , times :: Maybe Int
                     , focus :: TranslateH Core Path
                     }

instance Default Target where
    def = Target { atPhase = Just $ Left 0 -- everything defaults to first phase
                 , times = Just 1
                 , focus = constT $ return []
                 }

data OInst :: * -> * where
    RR       :: RewriteH Core                     -> OInst ()
    Query    :: TranslateH Core a                 -> OInst a
    Shell    :: [External] -> [CommandLineOption] -> OInst ()
    SetT     :: (Target -> Target)                -> OInst Target -- returns previous target
    IOAction :: IO a                              -> OInst a

-- using operational, but would we nice to use Neil's constrained-normal package!
-- Also, we use it with a newtype instead of a type synonym like normal,
-- so we can declare a MonadIO instance!
newtype OM a = OM { unOM :: Program OInst a }

-- class Monad m => MonadIO m where
instance Monad OM where
    return = OM . return
    (OM m) >>= k = OM (m >>= unOM . k)

instance MonadIO OM where
    liftIO = OM . singleton . IOAction

optimize :: ([CommandLineOption] -> OM ()) -> Plugin
optimize f = hermitPlugin $ \ pi -> runOM pi . f

runOM :: PhaseInfo -> OM () -> ModGuts -> CoreM ModGuts
runOM pi comp = scopedKernel $ \ kernel initSAST ->
    let env = mkHermitMEnv $ liftIO . debug
        debug (DebugTick msg) = putStrLn msg
        debug (DebugCore msg _c _e) = putStrLn $ "Core: " ++ msg

        errorAbort err = putStrLn err >> abortS kernel

        active :: Target -> Bool
        active t = maybe True (either (== phaseNum pi) (`elem` phasesDone pi)) $ atPhase t

        go :: Target -> Program OInst () -> SAST -> IO ()
        go t m sast | active t =
            case view m of
                Return a            -> resumeS kernel sast >>= runKureM return errorAbort
                RR rr       :>>= k  -> applyS kernel sast (focus t >>= flip pathR (extractR rr)) env
                                        >>= runKureM (go t (k ())) errorAbort
                Query tr    :>>= k  -> queryS kernel sast (focus t >>= flip pathT (extractT tr)) env
                                        >>= runKureM (\ x -> go t (k x) sast) errorAbort
                -- TODO: rework shell so it can return to k
                Shell es os :>>= _k -> Shell.interactive os defaultBehavior es kernel sast
                IOAction m  :>>= k  -> m >>= \ x -> go t (k x) sast
                SetT f      :>>= k  -> go (f t) (k t) sast
                    | otherwise = resumeS kernel sast >>= runKureM return errorAbort
    in go def (unOM comp) initSAST

interactive :: [External] -> [CommandLineOption] -> OM ()
interactive es os = OM . singleton $ Shell es os

run :: RewriteH Core -> OM ()
run = OM . singleton . RR

query :: TranslateH Core a -> OM a
query = OM . singleton . Query

------------------------ target modifiers -------------------------

setTarget :: (Target -> Target) -> OM Target
setTarget = OM . singleton . SetT

modifyTarget :: (Target -> Target) -> OM a -> OM a
modifyTarget f m = do
    t' <- setTarget f
    r <- m
    _ <- setTarget (const t')
    return r

at :: TranslateH Core Path -> OM a -> OM a
at tr = modifyTarget (\t -> t { focus = tr })

phase :: Int -> OM a -> OM a
phase n = modifyTarget (\t -> t { atPhase = Just (Left n) })

allPhases :: OM a -> OM a
allPhases = modifyTarget (\t -> t { atPhase = Nothing })
