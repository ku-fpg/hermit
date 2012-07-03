{-# LANGUAGE GADTs, RankNTypes, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable #-}

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

import GhcPlugins hiding (singleton)

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
        { resumeK ::            AST                      -> IO ()    -- ^ Halt the 'Kernel' and return control to GHC, which compiles the specified 'AST'.
        , abortK  ::                                        IO ()    -- ^ Halt the 'Kernel' and abort GHC without compiling.
        , applyK  ::            AST -> RewriteH Core     -> IO AST   -- ^ Apply a 'Rewrite' to the specified 'AST' and return a handle to the resulting 'AST'.
        , queryK  :: forall a . AST -> TranslateH Core a -> IO a     -- ^ Apply a 'TranslateH' to the 'AST' and return the resulting value.
        , deleteK ::            AST                      -> IO ()    -- ^ Delete the internal record of the specified 'AST'.
        , listK   ::                                        IO [AST] -- ^ List all the 'AST's tracked by the 'Kernel'.
        }

-- | A /handle/ for a specific version of the 'ModGuts'.
newtype AST = AST Int -- ^ Currently 'AST's are identified by an 'Int' label.
              deriving (Eq, Ord, Show)

data Msg s r = forall a . Req (s -> CoreM (Either String (a,s))) (MVar (Either String a))
             | Done (s -> CoreM r)

-- | Start a HERMIT client by providing an IO function that takes the initial 'Kernel' and inital 'AST' handle.
--   The 'Modguts' to 'CoreM' Modguts' function required by GHC Plugins is returned.
--   The callback is only ever called once.
hermitKernel :: (Kernel -> AST -> IO ()) -> ModGuts -> CoreM ModGuts
hermitKernel callback modGuts = do

        msg :: MVar (Msg (Map AST ModGuts) ModGuts) <- liftIO newEmptyMVar

        syntax_names :: MVar AST <- liftIO newEmptyMVar

        _ <- liftIO $ forkIO $ let loop n = do putMVar syntax_names (AST n)
                                               loop (succ n)
                                in loop 0

        let sendDone :: (Map AST ModGuts -> CoreM ModGuts) -> IO ()
            sendDone = putMVar msg . Done

        let sendReq :: (Map AST ModGuts -> CoreM (Either String (a,Map AST ModGuts))) -> IO a
            sendReq fn = do rep <- newEmptyMVar
                            putMVar msg (Req fn rep)
                            takeMVar rep >>= either fail return

        let kernel = Kernel
                { resumeK = \ name -> sendDone $ \ env -> find name env fail return
                , abortK  = sendDone $ \ _ -> throwGhcException (ProgramError "Exiting HERMIT and aborting GHC compilation.")
                , applyK = \ name rr -> sendReq $ \ env -> find name env fail' $ \ core ->
                             runHM
                                  (\ core' -> do
                                      syn' <- liftIO $ takeMVar syntax_names
                                      return' (syn',insert syn' core' env))
                                  fail'
                                  (apply (extractR rr) (initContext core) core)
                , queryK = \ name q -> sendReq $ \ env -> find name env fail' $ \ core ->
                             runHM
                                  (\ reply -> return' (reply,env))
                                  fail'
                                  (apply (extractT q) (initContext core) core)
                , deleteK = \ name -> sendReq $ \ env -> find name env fail' $ \ _ ->
                             return' ((), delete name env)
                , listK = sendReq $ \ env -> return' (keys env,env)
                }

        -- We always start with syntax blob 0
        syn <- liftIO $ takeMVar syntax_names

        let loop st = do
                m <- liftIO $ takeMVar msg
                case m of
                  Req fn rep -> do ans <- fn st
                                   case ans of
                                     Right (a,st2) -> do liftIO $ putMVar rep (Right a)
                                                         loop st2
                                     Left m' -> do liftIO $ putMVar rep (Left m')
                                                   loop st
                  Done fn -> fn st

        _pid <- liftIO $ forkIO $ callback kernel syn

        loop (singleton syn modGuts)

        -- (Kill the pid'd thread? do we need to?)


find :: Monad m => AST -> Map AST ModGuts -> (String -> m a) -> (ModGuts -> m a) -> m a
find name env failing k = maybe (failing $ "cannot find syntax tree : " ++ show name) k (lookup name env)

fail' :: Monad m => a -> m (Either a b)
fail' = return . Left

return' :: Monad m => b -> m (Either a b)
return' = return . Right
