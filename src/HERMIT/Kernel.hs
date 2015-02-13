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

import Control.Concurrent
import Control.Monad
import Control.Monad.IO.Class

import Data.Map

import HERMIT.Context
import HERMIT.Equality
import HERMIT.GHC hiding (singleton, empty)
import HERMIT.Kure
import HERMIT.Monad

-- | A 'Kernel' is a repository for complete Core syntax trees ('ModGuts').
--   For now, operations on a 'Kernel' are sequential, but later
--   it will be possible to have two 'applyK's running in parallel.
data Kernel = Kernel
  { resumeK :: MonadIO m => AST                                      -> m ()          -- ^ Halt the 'Kernel' and return control to GHC, which compiles the specified 'AST'.
  , abortK  :: MonadIO m =>                                             m ()          -- ^ Halt the 'Kernel' and abort GHC without compiling.
  , applyK  :: MonadIO m => AST -> RewriteH ModGuts     -> KernelEnv -> m (KureM AST) -- ^ Apply a 'Rewrite' to the specified 'AST' and return a handle to the resulting 'AST'.
  , queryK  :: MonadIO m => AST -> TransformH ModGuts a -> KernelEnv -> m (KureM (AST,a)) -- ^ Apply a 'TransformH' to the 'AST', return the resulting value, and potentially a new 'AST'.
  , deleteK :: MonadIO m => AST                                      -> m ()          -- ^ Delete the internal record of the specified 'AST'.
  , listK   :: MonadIO m =>                                             m [AST]       -- ^ List all the 'AST's tracked by the 'Kernel'.
  }

-- | A /handle/ for a specific version of the 'ModGuts'.
newtype AST = AST Int -- ^ Currently 'AST's are identified by an 'Int' label.
    deriving (Eq, Ord, Show)

-- for succ
instance Enum AST where
    toEnum = AST
    fromEnum (AST i) = i

data ASTMap = ASTMap { astNext :: AST
                     , astMap  :: Map AST KernelState
                     }

data KernelState = KernelState { _ksLemmas :: Lemmas
                               , ksGuts   :: ModGuts
                               }

fromHermitMResult :: HermitMResult ModGuts -> KernelState
fromHermitMResult hRes = KernelState (hResLemmas hRes) (hResult hRes)

data KernelEnv = KernelEnv { kEnvChan :: DebugMessage -> HermitM () }

data Msg where
    Apply  :: AST -> (KernelState -> CoreM (KureM (Maybe KernelState, a)))
                  -> (MVar (KureM (AST, a))) -> Msg
    Read   :: (Map AST KernelState -> IO ()) -> Msg
    Delete :: AST                            -> Msg
    Done   :: Maybe AST                      -> Msg

-- | Put a 'KernelState' in the 'ASTMap', returning
-- the 'AST' to which it was assigned.
insertAST :: KernelState -> ASTMap -> (AST, ASTMap)
insertAST ks (ASTMap k m) = (k, ASTMap (succ k) (insert k ks m))

findAST :: AST -> Map AST KernelState -> (String -> b) -> (KernelState -> b) -> b
findAST ast m f = find ast m (f $ "Cannot find syntax tree: " ++ show ast)

-- | Start a HERMIT client by providing an IO callback that takes the
--   initial 'Kernel' and inital 'AST' handle. The callback is only
--   ever called once. The 'Modguts' to 'CoreM Modguts' function
--   required by GHC Plugins is returned.
hermitKernel :: (Kernel -> AST -> IO ()) -> ModGuts -> CoreM ModGuts
hermitKernel callback modGuts = do

    msgMV :: MVar Msg <- liftIO newEmptyMVar

    let withAST :: MonadIO m => AST -> (KernelState -> CoreM (KureM (Maybe KernelState, a))) -> m (KureM (AST, a))
        withAST ast k = liftIO $ do
            resVar <- newEmptyMVar
            putMVar msgMV $ Apply ast k resVar
            takeMVar resVar

        readOnly :: MonadIO m => (Map AST KernelState -> KureM a) -> m (KureM a)
        readOnly f = liftIO $ do
            resVar <- newEmptyMVar
            putMVar msgMV (Read (runKureM (putMVar resVar . return)
                                          (putMVar resVar . fail) . f))
            takeMVar resVar

    let kernel :: Kernel
        kernel = Kernel
            { resumeK = liftIO . putMVar msgMV . Done . Just

            , abortK  = liftIO $ putMVar msgMV (Done Nothing)

            , applyK = \ ast rr kEnv -> liftM (liftM fst) $
                            withAST ast $ \ (KernelState lemmas guts) ->
                                runHM (kEnvChan kEnv)
                                      (mkEnv guts lemmas)
                                      (return . return . (,()) . Just . fromHermitMResult)
                                      (return . fail)
                                      (applyT rr (topLevelHermitC guts) guts)

            , queryK = \ ast t kEnv ->
                            withAST ast $ \ (KernelState lemmas guts) -> do
                                let handleS hRes
                                        | hResChanged hRes = return $ return (Just (KernelState (hResLemmas hRes) guts), r)
                                        | otherwise        = return $ return (Nothing, r)
                                        where r = hResult hRes
                                runHM (kEnvChan kEnv)
                                      (mkEnv guts lemmas)
                                      handleS
                                      (return . fail)
                                      (applyT t (topLevelHermitC guts) guts)

            , deleteK = liftIO . putMVar msgMV . Delete

            , listK = readOnly (return . keys) >>= runKureM return fail
            }

    let loop :: ASTMap -> CoreM ModGuts
        loop st = do
            m <- liftIO $ takeMVar msgMV
            case m of
              Apply ast f resVar -> do
                kr <- findAST ast (astMap st) (return . fail) f
                let handleS (mbKS, r) =
                        case mbKS of
                            Nothing -> do
                                liftIO $ putMVar resVar $ return (ast,r)
                                loop st
                            Just ks -> do
                                let (ast', st') = insertAST ks st
                                liftIO $ putMVar resVar $ return (ast',r)
                                loop st'
                    handleF msg = do
                        liftIO $ putMVar resVar (fail msg)
                        loop st
                runKureM handleS handleF kr
              Read fn -> liftIO (fn (astMap st)) >> loop st
              Delete ast -> loop $ ASTMap (astNext st) $ delete ast (astMap st)
              Done mbAST ->
                case mbAST of
                    Nothing  ->
                        abortKernel "Exiting HERMIT and aborting GHC compilation."
                    Just ast ->
                        findAST ast (astMap st)
                            (\msg -> abortKernel $ msg ++ ", exiting HERMIT and aborting GHC compilation.")
                            (return . ksGuts)

    -- We always start with AST 0
    let ast0 = AST 0

    _pid <- liftIO $ forkIO $ callback kernel ast0

    loop (ASTMap (AST 1) $ singleton ast0 $ KernelState empty modGuts)

    -- (Kill the pid'd thread? do we need to?)

abortKernel :: String -> CoreM a
abortKernel = throwGhcException . ProgramError

find :: Ord k => k -> Map k v -> b -> (v -> b) -> b
find k m f s = maybe f s (lookup k m)
