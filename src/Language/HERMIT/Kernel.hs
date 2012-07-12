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
  { resumeK ::            AST                      -> IO ()                -- ^ Halt the 'Kernel' and return control to GHC, which compiles the specified 'AST'.
  , abortK  ::                                        IO ()                -- ^ Halt the 'Kernel' and abort GHC without compiling.
  , applyK  ::            AST -> RewriteH Core     -> IO (KureMonad AST)   -- ^ Apply a 'Rewrite' to the specified 'AST' and return a handle to the resulting 'AST'.
  , queryK  :: forall a . AST -> TranslateH Core a -> IO (KureMonad a)     -- ^ Apply a 'TranslateH' to the 'AST' and return the resulting value.
  , deleteK ::            AST                      -> IO ()                -- ^ Delete the internal record of the specified 'AST'.
  , listK   ::                                        IO [AST]             -- ^ List all the 'AST's tracked by the 'Kernel'.
  }

-- | A /handle/ for a specific version of the 'ModGuts'.
newtype AST = AST Int -- ^ Currently 'AST's are identified by an 'Int' label.
              deriving (Eq, Ord, Show)

data Msg s r = forall a . Req (s -> HermitM (a,s)) (MVar (KureMonad a))
             | Done (s -> CoreM r)

-- | Start a HERMIT client by providing an IO function that takes the initial 'Kernel' and inital 'AST' handle.
--   The 'Modguts' to 'CoreM' Modguts' function required by GHC Plugins is returned.
--   The callback is only ever called once.
hermitKernel :: (Kernel -> AST -> IO ()) -> ModGuts -> CoreM ModGuts
hermitKernel callback modGuts = do

        msgMV :: MVar (Msg (Map AST ModGuts) ModGuts) <- liftIO newEmptyMVar

        syntax_names :: MVar AST <- liftIO newEmptyMVar

        _ <- liftIO $ forkIO $ let loop n = do putMVar syntax_names (AST n)
                                               loop (succ n)
                                in loop 0

        let sendDone :: (Map AST ModGuts -> CoreM ModGuts) -> IO ()
            sendDone = putMVar msgMV . Done

        let sendReq :: (Map AST ModGuts -> HermitM (a, Map AST ModGuts)) -> IO (KureMonad a)
            sendReq fn = do rep  <- newEmptyMVar
                            putMVar msgMV (Req fn rep)
                            takeMVar rep


        let kernel :: Kernel
            kernel = Kernel
                { resumeK = \ name -> sendDone $ \ env -> findWithErrMsg name env (\ msg -> throwGhcException $ ProgramError $ msg ++ ", exiting HERMIT and aborting GHC compilation.") return

                , abortK  = sendDone $ \ _ -> throwGhcException (ProgramError "Exiting HERMIT and aborting GHC compilation.")

                , applyK = \ name r -> sendReq $ \ env -> findWithErrMsg name env fail $ \ core -> do core' <- apply (extractR r) (initContext core) core
                                                                                                      syn' <- liftIO $ takeMVar syntax_names
                                                                                                      return (syn', insert syn' core' env)

                , queryK = \ name q -> sendReq $ \ env -> findWithErrMsg name env fail $ \ core -> do reply <- apply (extractT q) (initContext core) core
                                                                                                      return (reply,env)

                , deleteK = \ name -> sendReq (\ env -> find name env (return ((), env))
                                                                      (\ _ -> return ((), delete name env)))
                                         >>= runKureMonad return fail

                , listK = sendReq (\ env -> return (keys env, env)) >>= runKureMonad return fail
                }

        -- We always start with syntax blob 0
        syn <- liftIO $ takeMVar syntax_names

        let loop :: LoopState -> CoreM ModGuts
            loop (asts, defs) = do
                m <- liftIO $ takeMVar msgMV
                case m of
                  Req fn rep -> runHM defs
                                      (\ defs' (a,asts') -> liftIO (putMVar rep $ return a) >> loop (asts', defs'))
                                      (\ msg             -> liftIO (putMVar rep $ fail msg) >> loop (asts , defs ))
                                      (fn asts)

                  Done fn -> fn asts

        _pid <- liftIO $ forkIO $ callback kernel syn

        loop (singleton syn modGuts, empty)

        -- (Kill the pid'd thread? do we need to?)

type LoopState = (Map AST ModGuts, DefStash)

findWithErrMsg :: AST -> Map AST v -> (String -> b) -> (v -> b) -> b
findWithErrMsg ast m f = find ast m (f $ "Cannot find syntax tree: " ++ show ast)

find :: Ord k => k -> Map k v -> b -> (v -> b) -> b
find k m f s = maybe f s (lookup k m)
