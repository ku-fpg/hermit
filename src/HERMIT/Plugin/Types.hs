{-# LANGUAGE TypeFamilies, DeriveDataTypeable, FlexibleContexts,
             LambdaCase, GADTs, GeneralizedNewtypeDeriving,
             ScopedTypeVariables, FlexibleInstances, CPP #-}
module HERMIT.Plugin.Types where

import Control.Applicative
import Control.Concurrent.STM
#if MIN_VERSION_mtl(2,2,1)
import Control.Monad.Except
#else
import Control.Monad.Error
#endif
import Control.Monad.State

import Data.Dynamic
import qualified Data.Map as M

import HERMIT.Kure
import HERMIT.External
import HERMIT.Kernel (KernelEnv(..))
import HERMIT.Kernel.Scoped
import HERMIT.Monad
import HERMIT.Plugin.Builder
import HERMIT.PrettyPrinter.Common

import System.IO

type PluginM = PluginT IO
#if MIN_VERSION_mtl(2,2,1)
newtype PluginT m a = PluginT { unPluginT :: ExceptT PException (StateT PluginState m) a }
#else
newtype PluginT m a = PluginT { unPluginT :: ErrorT PException (StateT PluginState m) a }
#endif
    deriving (Functor, Applicative, Monad, MonadIO, MonadError PException, MonadState PluginState)

runPluginT :: PluginState -> PluginT m a -> m (Either PException a, PluginState)
#if MIN_VERSION_mtl(2,2,1)
runPluginT ps = flip runStateT ps . runExceptT . unPluginT
#else
runPluginT ps = flip runStateT ps . runErrorT . unPluginT
#endif

instance MonadTrans PluginT where
    lift = PluginT . lift . lift

instance Monad m => MonadCatch (PluginT m) where
    -- law: fail msg `catchM` f == f msg
    -- catchM :: m a -> (String -> m a) -> m a
    catchM m f = do
        st <- get
        (r,st') <- lift $ runPluginT st m
        case r of
            Left err -> case err of
                            PError msg -> f msg
                            other -> throwError other -- rethrow abort/resume
            Right v  -> put st' >> return v

-- Session-local issues; things that are never saved.
data PluginState = PluginState
    { ps_cursor         :: SAST                                     -- ^ the current AST
    , ps_pretty         :: PrettyPrinter                            -- ^ which pretty printer to use
    , ps_render         :: Handle -> PrettyOptions -> Either String DocH -> IO () -- ^ the way of outputing to the screen
    , ps_tick           :: TVar (M.Map String Int)                  -- ^ the list of ticked messages
    , ps_corelint       :: Bool                                     -- ^ if true, run Core Lint on module after each rewrite
    , ps_diffonly       :: Bool                                     -- ^ if true, show diffs rather than pp full code (TODO: move into pretty opts)
    , ps_failhard       :: Bool                                     -- ^ if true, abort on *any* failure
    -- this should be in a reader
    , ps_kernel         :: ScopedKernel
    , ps_phase          :: PhaseInfo
    } deriving (Typeable)

data PException = PAbort | PResume SAST | PError String

#if !(MIN_VERSION_mtl(2,2,1))
instance Error PException where strMsg = PError
#endif

newtype PSBox = PSBox PluginState deriving Typeable
instance Extern PluginState where
    type Box PluginState = PSBox
    unbox (PSBox st) = st
    box = PSBox

-- tick counter
tick :: TVar (M.Map String Int) -> String -> IO Int
tick var msg = atomically $ do
        m <- readTVar var
        let c = case M.lookup msg m of
                Nothing -> 1
                Just x  -> x + 1
        writeTVar var (M.insert msg c m)
        return c

mkKernelEnv :: PluginState -> KernelEnv
mkKernelEnv st =
    let pp = ps_pretty st
        out str = liftIO $ ps_render st stdout (pOptions pp) (Left $ str ++ "\n")

    in  KernelEnv $ \ msg -> case msg of
                DebugTick    msg'      -> do
                        c <- liftIO $ tick (ps_tick st) msg'
                        out $ "<" ++ show c ++ "> " ++ msg'
                DebugCore  msg' cxt core -> do
                        out $ "[" ++ msg' ++ "]"
                        doc :: DocH <- applyT (pCoreTC pp) (liftPrettyC (pOptions pp) cxt) (inject core)
                        liftIO $ ps_render st stdout (pOptions pp) (Right doc)

iokm' :: (MonadIO m, MonadCatch m) => String -> (a -> m b) -> IO (KureM a) -> m b
iokm' msg ret m = liftIO m >>= runKureM ret (fail . (msg ++))

iokm :: (MonadIO m, MonadCatch m) => String -> IO (KureM a) -> m a
iokm msg = iokm' msg return

iokm'' :: (MonadIO m, MonadCatch m) => IO (KureM a) -> m a
iokm'' = iokm ""
