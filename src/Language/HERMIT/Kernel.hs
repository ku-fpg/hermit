{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, DeriveDataTypeable, TupleSections #-}

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

-- | A 'Kernel' is a repository for complete Core syntax trees ('ModGuts').
--   For now, operations on a 'Kernel' are sequential, but later
--   it will be possible to have two 'applyK's running in parallel.
data Kernel = Kernel
  { resumeK ::            AST                                        -> IO ()           -- ^ Halt the 'Kernel' and return control to GHC, which compiles the specified 'AST'.
  , abortK  ::                                                          IO ()           -- ^ Halt the 'Kernel' and abort GHC without compiling.
  , applyK  ::            AST -> RewriteH ModGuts     -> HermitMEnv  -> IO (KureM AST)  -- ^ Apply a 'Rewrite' to the specified 'AST' and return a handle to the resulting 'AST'.
  , queryK  :: forall a . AST -> TranslateH ModGuts a -> HermitMEnv  -> IO (KureM a)    -- ^ Apply a 'TranslateH' to the 'AST' and return the resulting value.
  , deleteK ::            AST                                        -> IO ()           -- ^ Delete the internal record of the specified 'AST'.
  , listK   ::                                                          IO [AST]        -- ^ List all the 'AST's tracked by the 'Kernel'.
  }

-- | A /handle/ for a specific version of the 'ModGuts'.
newtype AST = AST Int -- ^ Currently 'AST's are identified by an 'Int' label.
              deriving (Eq, Ord, Show)

data Msg s r = forall a . Req (s -> CoreM (KureM (a,s))) (MVar (KureM a))
             | Done (s -> CoreM r)

type KernelState = Map AST (DefStash, ModGuts)

-- | Start a HERMIT client by providing an IO function that takes the initial 'Kernel' and inital 'AST' handle.
--   The 'Modguts' to 'CoreM' Modguts' function required by GHC Plugins is returned.
--   The callback is only ever called once.
hermitKernel :: (Kernel -> AST -> IO ()) -> ModGuts -> CoreM ModGuts
hermitKernel callback modGuts = do

        msgMV :: MVar (Msg KernelState ModGuts) <- liftIO newEmptyMVar

        nextASTname :: MVar AST <- liftIO newEmptyMVar

        _ <- liftIO $ forkIO $ let loop n = do putMVar nextASTname (AST n)
                                               loop (succ n)
                                in loop 0

        let sendDone :: (KernelState -> CoreM ModGuts) -> IO ()
            sendDone = putMVar msgMV . Done

        let sendReq :: (KernelState -> CoreM (KureM (a, KernelState))) -> IO (KureM a)
            sendReq fn = do rep  <- newEmptyMVar
                            putMVar msgMV (Req fn rep)
                            takeMVar rep

        let sendReqRead :: (KernelState -> CoreM (KureM a)) -> IO (KureM a)
            sendReqRead fn = sendReq (\ st -> (fmap.fmap) (,st) $ fn st)

        let sendReqWrite :: (KernelState -> CoreM KernelState) -> IO ()
            sendReqWrite fn = sendReq (fmap ( return . ((),) ) . fn) >>= runKureM return fail

        let kernel :: Kernel
            kernel = Kernel
                { resumeK = \ name -> sendDone $ \ st -> findWithErrMsg name st (\ msg -> throwGhcException $ ProgramError $ msg ++ ", exiting HERMIT and aborting GHC compilation.") (return.snd)

                , abortK  = sendDone $ \ _ -> throwGhcException (ProgramError "Exiting HERMIT and aborting GHC compilation.")

                , applyK = \ name r hm_env -> sendReq $ \ st -> findWithErrMsg name st fail $ \ (defs, guts) -> runHM hm_env
                                                                                                               defs
                                                                                                               (\ defs' guts' -> do ast <- liftIO $ takeMVar nextASTname
                                                                                                                                    return $ return (ast, insert ast (defs',guts') st))
                                                                                                               (return . fail)
                                                                                                               (apply r (initHermitC guts) guts)

                , queryK = \ name t hm_env -> sendReqRead $ \ st -> findWithErrMsg name st fail $ \ (defs, core) -> runHM hm_env
                                                                                                                      defs
                                                                                                                      (\ _ -> return.return)
                                                                                                                      (return . fail)
                                                                                                                      (apply t (initHermitC core) core)

                , deleteK = \ name -> sendReqWrite (return . delete name)

                , listK = sendReqRead (return . return . keys) >>= runKureM return fail
                }

        -- We always start with AST 0
        ast0 <- liftIO $ takeMVar nextASTname

        let loop :: KernelState -> CoreM ModGuts
            loop st = do
                m <- liftIO $ takeMVar msgMV
                case m of
                  Req fn rep -> fn st >>= runKureM (\ (a,st') -> liftIO (putMVar rep $ return a) >> loop st')
                                                   (\ msg     -> liftIO (putMVar rep $ fail msg) >> loop st)
                  Done fn -> fn st

        _pid <- liftIO $ forkIO $ callback kernel ast0

        loop (singleton ast0 (empty, modGuts))

        -- (Kill the pid'd thread? do we need to?)

findWithErrMsg :: AST -> Map AST v -> (String -> b) -> (v -> b) -> b
findWithErrMsg ast m f = find ast m (f $ "Cannot find syntax tree: " ++ show ast)

find :: Ord k => k -> Map k v -> b -> (v -> b) -> b
find k m f s = maybe f s (lookup k m)
