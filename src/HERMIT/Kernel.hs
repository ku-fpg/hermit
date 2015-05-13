{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module HERMIT.Kernel
    ( -- * The HERMIT Kernel
      AST
    , firstAST
    , ASTMap
    , Kernel
    , KernelEnv(..)
    , hermitKernel
    , CommitMsg(..)
      -- ** Kernel Interface
    , resumeK
    , abortK
    , applyK
    , queryK
    , deleteK
    , listK
    , tellK
    ) where

import Prelude hiding (lookup, null)

import Control.Concurrent
import Control.Monad
import Control.Monad.IO.Class

import Data.IORef
import Data.Map
import Data.Typeable

import HERMIT.Context
import HERMIT.External
import HERMIT.GHC hiding (singleton, empty)
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Monad

-- | A 'Kernel' is a repository for complete Core syntax trees ('ModGuts') and Lemmas.
data Kernel = Kernel
  { -- | Halt the 'Kernel' and return control to GHC, which compiles the specified 'AST'.
    resumeK :: forall m. MonadIO m =>                                   AST -> m ()
    -- | Halt the 'Kernel' and abort GHC without compiling.
  , abortK  :: forall m. MonadIO m =>                                          m ()
    -- | Apply a 'Rewrite' to the specified 'AST' and return a handle to the resulting 'AST'.
  , applyK  :: forall m. (MonadIO m, MonadCatch m)
            => RewriteH ModGuts     -> CommitMsg -> KernelEnv ->        AST -> m AST
    -- | Apply a 'TransformH' to the 'AST', return the resulting value, and potentially a new 'AST'.
  , queryK  :: forall m a. (MonadIO m, MonadCatch m)
            => TransformH ModGuts a -> CommitMsg -> KernelEnv ->        AST -> m (AST,a)
    -- | Delete the internal record of the specified 'AST'.
  , deleteK :: forall m. MonadIO m =>                                   AST -> m ()
    -- | List all the 'AST's tracked by the 'Kernel', including version data.
  , listK   :: forall m. MonadIO m =>                                          m [(AST,Maybe String, Maybe AST)]
    -- | Log a new AST with same Lemmas/ModGuts as given AST.
  , tellK   :: forall m. (MonadIO m, MonadCatch m) => String         -> AST -> m AST
  }

data CommitMsg = Always String | Changed String | Never

msg :: CommitMsg -> Maybe String
msg Never = Nothing
msg (Always s) = Just s
msg (Changed s) = Just s

-- | A /handle/ for a specific version of the 'ModGuts'.
newtype AST = AST Int -- ^ Currently 'AST's are identified by an 'Int' label.
    deriving (Eq, Ord, Typeable)

firstAST :: AST
firstAST = AST 0

-- for succ
instance Enum AST where
    toEnum = AST
    fromEnum (AST i) = i

instance Show AST where
    show (AST i) = show i

instance Read AST where
    readsPrec p s = [ (AST i,s') | (i,s') <- readsPrec p s ]

instance Extern AST where
    type Box AST = AST
    box i = i
    unbox i = i

data ASTMap = ASTMap { astNext :: AST
                     , astMap  :: Map AST KernelState
                     }

emptyASTMap :: ASTMap
emptyASTMap = ASTMap firstAST empty

data KernelState = KernelState { ksLemmas  :: Lemmas
                               , ksGuts    :: ModGuts
                               , _ksParent :: Maybe AST
                               , _ksCommit :: Maybe String
                               }

data KernelEnv = KernelEnv { kEnvChan :: KEnvMessage -> HermitM () }

-- | Internal API. The 'Kernel' object wraps these calls.
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
--   ever called once. The 'Modguts -> CoreM Modguts' function
--   required by GHC Plugins is returned.
hermitKernel :: IORef (Maybe (AST, ASTMap)) -- ^ Global (across passes) AST store.
             -> String                      -- ^ Last GHC pass name
             -> (Kernel -> AST -> IO ())    -- ^ Callback
             -> ModGuts -> CoreM ModGuts
hermitKernel store lastPass callback modGuts = do

    msgMV :: MVar Msg <- liftIO newEmptyMVar

    let withAST :: (MonadIO m, MonadCatch m)
                => AST -> (KernelState -> CoreM (KureM (Maybe KernelState, a))) -> m (AST, a)
        withAST ast k = do
            r <- liftIO $ do
                    resVar <- newEmptyMVar
                    putMVar msgMV $ Apply ast k resVar
                    takeMVar resVar
            runKureM return fail r

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

            , applyK = \ rr cm kEnv ast -> liftM fst $
                            withAST ast $ \ (KernelState lemmas guts _ _) -> do
                                let handleS hRes = return $ return
                                                   (Just (KernelState (hResLemmas hRes) (hResult hRes) (Just ast) (msg cm)), ())
                                runHM (mkEnv (kEnvChan kEnv) guts lemmas)
                                      handleS
                                      (return . fail)
                                      (applyT rr (topLevelHermitC guts) guts)

            , queryK = \ t cm kEnv ast ->
                            withAST ast $ \ (KernelState lemmas guts _ _) -> do
                                let handleS hRes
                                        | hResChanged hRes = f (Just (KernelState (hResLemmas hRes) guts (Just ast) (msg cm)), r)
                                        | Always s <- cm   = f (Just (KernelState lemmas guts (Just ast) (Just s)), r)
                                        | otherwise        = f (Nothing, r) -- pure query, not recorded in AST store
                                        where r = hResult hRes
                                              f = return . return
                                runHM (mkEnv (kEnvChan kEnv) guts lemmas)
                                      handleS
                                      (return . fail)
                                      (applyT t (topLevelHermitC guts) guts)

            , deleteK = liftIO . putMVar msgMV . Delete

            , listK = readOnly (\m -> return [ (ast,cm,p) | (ast,KernelState _ _ p cm) <- toList m ])
                        >>= runKureM return fail

            , tellK = \ str ast -> liftM fst $
                            withAST ast $ \ (KernelState lemmas guts _ _) ->
                                return $ return (Just $ KernelState lemmas guts (Just ast) (Just str), ())
            }

    let loop :: ASTMap -> CoreM ModGuts
        loop m = do
            cmd <- liftIO $ takeMVar msgMV
            case cmd of
              Apply ast f resVar -> do
                kr <- findAST ast (astMap m) (return . fail) f
                let handleS (mbKS, r) =
                        case mbKS of
                            Nothing -> liftIO (putMVar resVar $ return (ast,r)) >> loop m
                            Just ks -> let (ast', m') = insertAST ks m in
                                       liftIO (putMVar resVar (return (ast',r))) >> loop m'
                    handleF str = liftIO (putMVar resVar $ fail str) >> loop m
                runKureM handleS handleF kr
              Read fn -> liftIO (fn (astMap m)) >> loop m
              Delete ast -> loop $ ASTMap (astNext m) $ delete ast (astMap m)
              Done mbAST ->
                case mbAST of
                    Nothing  ->
                        abortKernel "Exiting HERMIT and aborting GHC compilation."
                    Just ast -> do
                        findAST ast (astMap m)
                            (\str -> abortKernel $ str ++ ", exiting HERMIT and aborting GHC compilation.")
                            (\ks -> liftIO (writeIORef store (Just (ast, m))) >> return (ksGuts ks))

    -- Get the most recent AST and ASTMap the last HERMIT pass resumed with.
    mbS <- liftIO $ readIORef store
    (ast0,m) <- case mbS of
        Nothing      -> return $ insertAST (KernelState empty modGuts Nothing Nothing) emptyASTMap
        Just (ast,m) -> do
            ls <- findAST ast (astMap m)
                    (\str -> abortKernel $ str ++ ", exiting HERMIT and aborting GHC compilation.")
                    (return . ksLemmas)
            return $ insertAST (KernelState ls modGuts (Just ast) (Just lastPass)) m

    void $ liftIO $ forkIO $ callback kernel ast0

    loop m

abortKernel :: String -> CoreM a
abortKernel = throwGhcException . ProgramError

find :: Ord k => k -> Map k v -> b -> (v -> b) -> b
find k m f s = maybe f s (lookup k m)
