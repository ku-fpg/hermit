{-# LANGUAGE KindSignatures, GADTs, RankNTypes, ScopedTypeVariables, TypeFamilies, DeriveDataTypeable #-}

module Language.HERMIT.Kernel
        (hermitKernel
        , Kernel(..)
        , AST(..)
        ) where

import GhcPlugins

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.GHC

import qualified Data.Map as M
import Control.Concurrent

data Kernel = Kernel
        { resumeK ::            AST                      -> IO ()
        , abortK  ::                                        IO ()
        , applyK  ::            AST -> RewriteH Core     -> IO AST
        , queryK  :: forall a . AST -> TranslateH Core a -> IO a
        , deleteK ::            AST                      -> IO ()
        , listK   ::                                        IO [AST]
        }

-- a name of a syntax tree
newtype AST = AST Int
        deriving (Eq, Ord, Show)

data Msg s r = forall a . Req (s -> CoreM (Either String (a,s))) (MVar (Either String a))
             | Done (s -> CoreM r)

-- | 'hermitKernel' is a repository for our syntax trees.
-- For now, operations are sequential, but later
-- it will be possible to have two applyK's running in parallel.
--
-- The callback is only every called once.
hermitKernel :: (Kernel -> AST -> IO ())
             -> ModGuts -> CoreM ModGuts
hermitKernel callback modGuts = do

        msg :: MVar (Msg (M.Map AST ModGuts) ModGuts) <- liftIO newEmptyMVar

        syntax_names :: MVar AST <- liftIO newEmptyMVar

        _ <- liftIO $ forkIO $
                let loop n = do
                        putMVar syntax_names (AST n)
                        loop (succ n)
                 in loop 0

        let sendDone :: (M.Map AST ModGuts -> CoreM ModGuts) -> IO ()
            sendDone = putMVar msg . Done

        let sendReq :: (M.Map AST ModGuts -> CoreM (Either String (a,M.Map AST ModGuts))) -> IO a
            sendReq fn = do
                rep <- newEmptyMVar
                putMVar msg (Req fn rep)
                res <- takeMVar rep
                case res of
                  Left m -> do
                        print ("sendReq",m)
                        fail m
                  Right ans -> return ans

        let find :: (Monad m) => AST -> M.Map AST ModGuts -> (String -> m a) -> (ModGuts -> m a) -> m a
            find name env failing k = case M.lookup name env of
              Nothing -> failing $ "can not find syntax tree : " ++ show name
              Just core -> k core

        let fail' m = return (Left m)

        let kernel = Kernel
                { resumeK = \ name -> sendDone $ \ env -> find name env fail $ \ core -> return core
                , abortK  = sendDone $ \ _ -> throwGhcException (ProgramError "<HERMIT>: hard GHC abort requested")
                , applyK = \ name rr -> sendReq $ \ env -> find name env fail' $ \ core ->
                             runHM
                                  (\ core' -> do
                                      syn' <- liftIO $ takeMVar syntax_names
                                      return $ Right (syn',M.insert syn' core' env))
                                  (\ m -> return $ Left m)
                                  (apply (extractR rr) (initHermitEnv core) core)
                , queryK = \ name q -> sendReq $ \ env -> find name env fail' $ \ core ->
                             runHM
                                  (\ reply -> return  $ Right (reply,env))
                                  (\ m -> return $ Left m)
                                  (apply (extractT q) (initHermitEnv core) core)
                , deleteK = \ name -> sendReq $ \ env -> find name env fail' $ \ _ ->
                             return $ Right ((), M.delete name env)
                , listK = sendReq $ \ env -> return $ Right (M.keys env,env)
                }

        -- We always start with syntax blob 0
        syn <- liftIO $ takeMVar syntax_names

        let loop st = do
                m <- liftIO $ takeMVar msg
                case m of
                  Req fn rep -> do
                          ans <- fn st
                          case ans of
                            Right (a,st2) -> do
                              liftIO $ putMVar rep (Right a)
                              loop st2
                            Left m' -> do
                              liftIO $ putMVar rep (Left m')
                              loop st
                  Done fn -> fn st

        _pid <- liftIO $ forkIO $ callback kernel syn

        modGuts' <- loop (M.singleton syn modGuts)

        -- (Kill the pid'd thread? do we need to?)

        return modGuts'

