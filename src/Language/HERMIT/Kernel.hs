{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable, TupleSections #-}

module Language.HERMIT.Kernel
        ( -- * The HERMIT Kernel
          AST
        , Kernel
        , hermitKernel
        , resumeK
        , abortK
        , applyK
        , queryK
        , deleteK
        , listK
) where

import Prelude hiding (lookup)

import GhcPlugins hiding (singleton, empty)

import Language.HERMIT.Context
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.GHC

import Data.Map
import Control.Concurrent

-- | A 'Kernel' is a repository for Core syntax trees.
--   For now, operations on a 'Kernel' are sequential, but later
--   it will be possible to have two 'applyK's running in parallel.
data Kernel = Kernel
  { resumeK ::            AST                                      -> IO ()                -- ^ Halt the 'Kernel' and return control to GHC, which compiles the specified 'AST'.
  , abortK  ::                                                        IO ()                -- ^ Halt the 'Kernel' and abort GHC without compiling.
  , applyK  ::            AST -> RewriteH Core     -> HermitMEnv   -> IO (KureMonad AST)   -- ^ Apply a 'Rewrite' to the specified 'AST' and return a handle to the resulting 'AST'.
  , queryK  :: forall a . AST -> TranslateH Core a -> HermitMEnv   -> IO (KureMonad a)     -- ^ Apply a 'TranslateH' to the 'AST' and return the resulting value.
  , deleteK ::            AST                                      -> IO ()                -- ^ Delete the internal record of the specified 'AST'.
  , listK   ::                                                        IO [AST]             -- ^ List all the 'AST's tracked by the 'Kernel'.
  }

-- | A /handle/ for a specific version of the 'ModGuts'.
newtype AST = AST Int -- ^ Currently 'AST's are identified by an 'Int' label.
              deriving (Eq, Ord, Show)

data Msg s r = forall a . Req (s -> CoreM (KureMonad (a,s))) (MVar (KureMonad a))
             | Done (s -> CoreM r)

type KernelState = Map AST (DefStash, ModGuts)

-- | Start a HERMIT client by providing an IO function that takes the initial 'Kernel' and inital 'AST' handle.
--   The 'Modguts' to 'CoreM' Modguts' function required by GHC Plugins is returned.
--   The callback is only ever called once.
hermitKernel :: (Kernel -> AST -> IO ()) -> ModGuts -> CoreM ModGuts
hermitKernel callback modGuts = do

        msgMV :: MVar (Msg KernelState ModGuts) <- liftIO newEmptyMVar

        syntax_names :: MVar AST <- liftIO newEmptyMVar

        _ <- liftIO $ forkIO $ let loop n = do putMVar syntax_names (AST n)
                                               loop (succ n)
                                in loop 0

        let sendDone :: (KernelState -> CoreM ModGuts) -> IO ()
            sendDone = putMVar msgMV . Done

        let sendReq :: (KernelState -> CoreM (KureMonad (a, KernelState))) -> IO (KureMonad a)
            sendReq fn = do rep  <- newEmptyMVar
                            putMVar msgMV (Req fn rep)
                            takeMVar rep

        let sendReqRead :: (KernelState -> CoreM (KureMonad a)) -> IO (KureMonad a)
            sendReqRead fn = sendReq (\ st -> (fmap.fmap) (,st) $ fn st)

        let sendReqWrite :: (KernelState -> CoreM KernelState) -> IO ()
            sendReqWrite fn = sendReq (fmap ( return . ((),) ) . fn) >>= runKureMonad return fail

        let kernel :: Kernel
            kernel = Kernel
                { resumeK = \ name -> sendDone $ \ st -> findWithErrMsg name st (\ msg -> throwGhcException $ ProgramError $ msg ++ ", exiting HERMIT and aborting GHC compilation.") (return.snd)

                , abortK  = sendDone $ \ _ -> throwGhcException (ProgramError "Exiting HERMIT and aborting GHC compilation.")

                , applyK = \ name r hm_env -> sendReq $ \ st -> findWithErrMsg name st fail $ \ (defs, core) -> runHM hm_env
                                                                                                               defs
                                                                                                               (\ defs' core' -> do syn' <- liftIO $ takeMVar syntax_names
                                                                                                                                    return $ return (syn', insert syn' (defs',core') st))
                                                                                                               (return . fail)
                                                                                                               (apply (extractR r) (initContext core) core)

                , queryK = \ name q hm_env -> sendReqRead $ \ st -> findWithErrMsg name st fail $ \ (defs, core) -> runHM hm_env
                                                                                                                   defs
                                                                                                                   (\ _ -> return.return)
                                                                                                                   (return . fail)
                                                                                                                   (apply (extractT q) (initContext core) core)

                , deleteK = \ name -> sendReqWrite (return . delete name)

                , listK = sendReqRead (return . return . keys) >>= runKureMonad return fail
                }

        -- We always start with syntax blob 0
        syn <- liftIO $ takeMVar syntax_names

        let loop :: KernelState -> CoreM ModGuts
            loop st = do
                m <- liftIO $ takeMVar msgMV
                case m of
                  Req fn rep -> fn st >>= runKureMonad (\ (a,st') -> liftIO (putMVar rep $ return a) >> loop st')
                                                       (\ msg     -> liftIO (putMVar rep $ fail msg) >> loop st)
                  Done fn -> fn st

        _pid <- liftIO $ forkIO $ callback kernel syn

        loop (singleton syn (empty, modGuts))

        -- (Kill the pid'd thread? do we need to?)

findWithErrMsg :: AST -> Map AST v -> (String -> b) -> (v -> b) -> b
findWithErrMsg ast m f = find ast m (f $ "Cannot find syntax tree: " ++ show ast)

find :: Ord k => k -> Map k v -> b -> (v -> b) -> b
find k m f s = maybe f s (lookup k m)
