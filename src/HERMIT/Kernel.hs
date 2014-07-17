{-# LANGUAGE RankNTypes, ScopedTypeVariables, TupleSections, GADTs #-}

module HERMIT.Kernel
    ( -- * The HERMIT Kernel
      AST
    , Kernel
    , KernelEnv(..)
    , hermitKernel
    , resumeK
    , abortK
    , applyK
    , queryK
    , deleteK
    , listK
    ) where

import Prelude hiding (lookup)

import HERMIT.Context
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.GHC hiding (singleton, empty)

import Data.Map
import Control.Concurrent

-- | A 'Kernel' is a repository for complete Core syntax trees ('ModGuts').
--   For now, operations on a 'Kernel' are sequential, but later
--   it will be possible to have two 'applyK's running in parallel.
data Kernel = Kernel
  { resumeK ::            AST                                      -> IO ()          -- ^ Halt the 'Kernel' and return control to GHC, which compiles the specified 'AST'.
  , abortK  ::                                                        IO ()          -- ^ Halt the 'Kernel' and abort GHC without compiling.
  , applyK  ::            AST -> RewriteH ModGuts     -> KernelEnv -> IO (KureM AST) -- ^ Apply a 'Rewrite' to the specified 'AST' and return a handle to the resulting 'AST'.
  , queryK  :: forall a . AST -> TransformH ModGuts a -> KernelEnv -> IO (KureM a)   -- ^ Apply a 'TransformH' to the 'AST' and return the resulting value.
  , deleteK ::            AST                                      -> IO ()          -- ^ Delete the internal record of the specified 'AST'.
  , listK   ::                                                        IO [AST]       -- ^ List all the 'AST's tracked by the 'Kernel'.
  }

-- | A /handle/ for a specific version of the 'ModGuts'.
newtype AST = AST Int -- ^ Currently 'AST's are identified by an 'Int' label.
              deriving (Eq, Ord, Show)

data Msg s r = forall a . Req (s -> CoreM (KureM (a,s))) (MVar (KureM a))
             | Done (s -> CoreM r)

type ASTMap = Map AST KernelState

data KernelState = KernelState { _ksStash  :: DefStash
                               , _ksLemmas :: Lemmas
                               , ksGuts   :: ModGuts
                               }

fromHermitMResult :: HermitMResult ModGuts -> KernelState
fromHermitMResult hRes = sideEffectsOnly hRes (hResult hRes)

sideEffectsOnly :: HermitMResult a -> ModGuts -> KernelState
sideEffectsOnly hRes = KernelState (hResStash hRes) (hResLemmas hRes)

data KernelEnv = KernelEnv { kEnvChan :: DebugMessage -> HermitM () }

-- | Start a HERMIT client by providing an IO function that takes the initial 'Kernel' and inital 'AST' handle.
--   The 'Modguts' to 'CoreM' Modguts' function required by GHC Plugins is returned.
--   The callback is only ever called once.
hermitKernel :: (Kernel -> AST -> IO ()) -> ModGuts -> CoreM ModGuts
hermitKernel callback modGuts = do

        msgMV :: MVar (Msg ASTMap ModGuts) <- liftIO newEmptyMVar

        nextASTname :: MVar AST <- liftIO newEmptyMVar

        _ <- liftIO $ forkIO $ let loop n = do putMVar nextASTname (AST n)
                                               loop (succ n)
                                in loop 0

        let sendDone :: (ASTMap -> CoreM ModGuts) -> IO ()
            sendDone = putMVar msgMV . Done

        let sendReq :: (ASTMap -> CoreM (KureM (a, ASTMap))) -> IO (KureM a)
            sendReq fn = do rep  <- newEmptyMVar
                            putMVar msgMV (Req fn rep)
                            takeMVar rep

        let sendReqRead :: (ASTMap -> CoreM (KureM a)) -> IO (KureM a)
            sendReqRead fn = sendReq (\ st -> (fmap.fmap) (,st) $ fn st) -- >>= return . fmap fst

        let sendReqWrite :: (ASTMap -> CoreM ASTMap) -> IO ()
            sendReqWrite fn = sendReq (fmap ( return . ((),) ) . fn) >>= {- fmap fst . -} liftKureM

        let kernel :: Kernel
            kernel = Kernel
                { resumeK = \ name ->
                                sendDone $ \ st ->
                                    findWithErrMsg name
                                                   st
                                                   (\ msg -> throwGhcException
                                                             $ ProgramError
                                                             $ msg ++ ", exiting HERMIT and aborting GHC compilation.")
                                                   (return.ksGuts)

                , abortK  = sendDone $ \ _ -> throwGhcException
                                              $ ProgramError "Exiting HERMIT and aborting GHC compilation."

                , applyK = \ name r kEnv ->
                                sendReq $ \ st ->
                                    findWithErrMsg name st fail $ \ (KernelState defs lemmas guts) ->
                                        runHM (kEnvChan kEnv)
                                              (mkEnv guts defs lemmas)
                                              (\ hRes -> do
                                                    ast <- liftIO $ takeMVar nextASTname
                                                    return $ return (ast, insert ast (fromHermitMResult hRes) st))
                                              (return . fail)
                                              (applyT r (topLevelHermitC guts) guts)

                , queryK = \ name t kEnv ->
                                sendReqRead $ \ st ->
                                    findWithErrMsg name st fail $ \ (KernelState defs lemmas guts) ->
                                        runHM (kEnvChan kEnv)
                                              (mkEnv guts defs lemmas)
                                              (return . return . hResult)
                                              (return . fail)
                                              (applyT t (topLevelHermitC guts) guts)

                , deleteK = \ name -> sendReqWrite (return . delete name)

                , listK = sendReqRead (return . return . keys) >>= liftKureM
                }

        -- We always start with AST 0
        ast0 <- liftIO $ takeMVar nextASTname

        let loop :: ASTMap -> CoreM ModGuts
            loop st = do
                m <- liftIO $ takeMVar msgMV
                case m of
                  Req fn rep -> fn st >>= runKureM (\ (a,st') -> liftIO (putMVar rep $ return a) >> loop st')
                                                   (\ msg     -> liftIO (putMVar rep $ fail msg) >> loop st)
                  Done fn -> fn st

        _pid <- liftIO $ forkIO $ callback kernel ast0

        loop (singleton ast0 $ KernelState empty empty modGuts)

        -- (Kill the pid'd thread? do we need to?)

findWithErrMsg :: AST -> Map AST v -> (String -> b) -> (v -> b) -> b
findWithErrMsg ast m f = find ast m (f $ "Cannot find syntax tree: " ++ show ast)

find :: Ord k => k -> Map k v -> b -> (v -> b) -> b
find k m f s = maybe f s (lookup k m)
