{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}

module HERMIT.Monad
    ( -- * The HERMIT Monad
      HermitM
    , runHM
    , embedHermitM
    , HermitMEnv
    , HermitMResult(..)
    , LiftCoreM(..)
    , runTcM
    , runDsM
      -- * Lemmas
    , HasLemmas(..)
    , addLemma
    , findLemma
    , insertLemma
      -- * Reader Information
    , HasHermitMEnv(..)
    , mkEnv
    , getModGuts
    , HasHscEnv(..)
      -- * Messages
    , HasDebugChan(..)
    , DebugMessage(..)
    , sendDebugMessage
    ) where

import Prelude hiding (lookup)

import Control.Applicative
import Control.Concurrent.STM
import Control.Monad
import Control.Monad.IO.Class

import Data.Map

import Language.KURE

import HERMIT.Core
import HERMIT.Context
import HERMIT.Equality
import HERMIT.Kure.SumTypes
import HERMIT.GHC
import HERMIT.GHC.Typechecker

----------------------------------------------------------------------------

-- | The HermitM environment.
data HermitMEnv = HermitMEnv { hEnvChanged   :: Bool -- ^ Whether Lemmas have changed
                             , hEnvModGuts   :: ModGuts -- ^ Note: this is a snapshot of the ModGuts from
                                                        --         before the current transformation.
                             , hEnvLemmas    :: Lemmas
                             }

mkEnv :: ModGuts -> Lemmas -> HermitMEnv
mkEnv = HermitMEnv False

-- | The HermitM result record.
data HermitMResult a = HermitMResult { hResChanged :: Bool -- ^ Whether Lemmas have changed
                                     , hResLemmas :: Lemmas
                                     , hResult    :: a
                                     }

changedResult :: Lemmas -> a -> HermitMResult a
changedResult = HermitMResult True

-- Does not change the Changed status of Lemmas
mkResult :: HermitMEnv -> a -> HermitMResult a
mkResult env = HermitMResult (hEnvChanged env) (hEnvLemmas env)

-- | The HERMIT monad is kept abstract.
--
-- It provides a reader for ModGuts, state for Lemmas,
-- and access to a debugging channel.
newtype HermitM a = HermitM { runHermitM :: DebugChan -> HermitMEnv -> CoreM (KureM (HermitMResult a)) }

type DebugChan = DebugMessage -> HermitM ()

-- | Eliminator for 'HermitM'.
runHM :: DebugChan                     -- debug chan
      -> HermitMEnv                    -- env
      -> (HermitMResult a -> CoreM b)  -- success
      -> (String -> CoreM b)           -- failure
      -> HermitM a                     -- ma
      -> CoreM b
runHM chan env success failure ma = runHermitM ma chan env >>= runKureM success failure

-- | Allow HermitM to be embedded in another monad with proper capabilities.
embedHermitM :: (HasDebugChan m, HasHermitMEnv m, HasLemmas m, LiftCoreM m) => HermitM a -> m a
embedHermitM hm = do
    env <- getHermitMEnv
    c <- liftCoreM $ liftIO newTChanIO -- we are careful to do IO within liftCoreM to avoid the MonadIO constraint
    r <- liftCoreM (runHermitM hm (liftIO . atomically . writeTChan c) env) >>= runKureM return fail
    chan <- getDebugChan
    let relayDebugMessages = do
            mm <- liftCoreM $ liftIO $ atomically $ tryReadTChan c
            case mm of
                Nothing -> return ()
                Just dm -> chan dm >> relayDebugMessages

    relayDebugMessages
    forM_ (toList (hResLemmas r)) $ uncurry insertLemma -- TODO: fix
    return $ hResult r

instance Functor HermitM where
  fmap :: (a -> b) -> HermitM a -> HermitM b
  fmap = liftM

instance Applicative HermitM where
  pure :: a -> HermitM a
  pure = return

  (<*>) :: HermitM (a -> b) -> HermitM a -> HermitM b
  (<*>) = ap

instance Monad HermitM where
  return :: a -> HermitM a
  return a = HermitM $ \ _ env -> return (return (mkResult env a))

  (>>=) :: HermitM a -> (a -> HermitM b) -> HermitM b
  (HermitM gcm) >>= f =
        HermitM $ \ chan env -> gcm chan env >>= runKureM (\ (HermitMResult c ls a) ->
                                                            let env' = env { hEnvChanged = c, hEnvLemmas = ls }
                                                            in  runHermitM (f a) chan env')
                                                          (return . fail)

  fail :: String -> HermitM a
  fail msg = HermitM $ \ _ _ -> return (fail msg)

instance MonadCatch HermitM where
  catchM :: HermitM a -> (String -> HermitM a) -> HermitM a
  (HermitM gcm) `catchM` f = HermitM $ \ chan env -> gcm chan env >>= runKureM (return.return)
                                                                               (\ msg -> runHermitM (f msg) chan env)

instance MonadIO HermitM where
  liftIO :: IO a -> HermitM a
  liftIO = liftCoreM . liftIO

instance MonadUnique HermitM where
  getUniqueSupplyM :: HermitM UniqSupply
  getUniqueSupplyM = liftCoreM getUniqueSupplyM

instance MonadThings HermitM where
    lookupThing :: Name -> HermitM TyThing
    -- We do not simply do:
    --
    --     lookupThing = liftCoreM . lookupThing
    --
    -- because we can do better. HermitM has access
    -- to the ModGuts, so we can find TyThings defined
    -- in the current module, not just imported ones.
    -- Usually we look in the context first, which has
    -- *most* things from the current module. However,
    -- some Ids, such as class method selectors, are not
    -- explicitly bound in the core, so will not be in
    -- the context. These are instead kept in the
    -- ModGuts' list of instances. Which this will find.
    lookupThing nm = runTcM $ tcLookupGlobal nm

instance HasDynFlags HermitM where
    getDynFlags :: HermitM DynFlags
    getDynFlags = liftCoreM getDynFlags

----------------------------------------------------------------------------

class HasHermitMEnv m where
    -- | Get the HermitMEnv
    getHermitMEnv :: m HermitMEnv

instance HasHermitMEnv HermitM where
    getHermitMEnv = HermitM $ \ _ env -> return $ return $ mkResult env env

getModGuts :: (HasHermitMEnv m, Monad m) => m ModGuts
getModGuts = liftM hEnvModGuts getHermitMEnv

----------------------------------------------------------------------------

class HasDebugChan m where
    -- | Get the debugging channel
    getDebugChan :: m (DebugMessage -> m ())

instance HasDebugChan HermitM where
    getDebugChan = HermitM $ \ chan env -> return $ return $ mkResult env chan

sendDebugMessage :: (HasDebugChan m, Monad m) => DebugMessage -> m ()
sendDebugMessage msg = getDebugChan >>= ($ msg)

----------------------------------------------------------------------------

class HasHscEnv m where
    getHscEnv :: m HscEnv

instance HasHscEnv CoreM where
    getHscEnv = getHscEnvCoreM

instance HasHscEnv HermitM where
    getHscEnv = liftCoreM getHscEnv

----------------------------------------------------------------------------

class HasLemmas m where
    getLemmas :: m Lemmas
    putLemmas :: Lemmas -> m ()

instance HasLemmas HermitM where
    getLemmas = HermitM $ \ _ env -> return $ return $ mkResult env (hEnvLemmas env)
    putLemmas m = HermitM $ \ _ _ -> return $ return $ changedResult m ()

-- | Insert or replace a lemma.
insertLemma :: (HasLemmas m, Monad m) => LemmaName -> Lemma -> m ()
insertLemma nm l = getLemmas >>= putLemmas . insert nm l

-- | Only adds a lemma if doesn't already exist.
addLemma :: (HasLemmas m, Monad m) => LemmaName -> Lemma -> m ()
addLemma nm l = do
    ls <- getLemmas
    maybe (insertLemma nm l) (\ _ -> return ()) (lookup nm ls)

-- | Find a lemma by name. Fails if lemma does not exist.
findLemma :: (HasLemmas m, Monad m) => LemmaName -> m Lemma
findLemma nm = do
    r <- liftM (lookup nm) getLemmas
    maybe (fail $ "lemma does not exist: " ++ show nm) return r

----------------------------------------------------------------------------

class Monad m => LiftCoreM m where
    -- | 'CoreM' can be lifted to this monad.
    liftCoreM :: CoreM a -> m a

instance LiftCoreM HermitM where
    liftCoreM coreM = HermitM $ \ _ env -> coreM >>= return . return . mkResult env

----------------------------------------------------------------------------

-- | A message packet.
data DebugMessage :: * where
    DebugTick ::                                       String                -> DebugMessage
    DebugCore :: (ReadBindings c, ReadPath c Crumb) => String -> c -> CoreTC -> DebugMessage

----------------------------------------------------------------------------

runTcM :: (HasDynFlags m, HasHermitMEnv m, HasHscEnv m, MonadIO m) => TcM a -> m a
runTcM m = do
    env <- getHscEnv
    dflags <- getDynFlags
    guts <- getModGuts
    -- What is the effect of HsSrcFile (should we be using something else?)
    -- What should the boolean flag be set to?
    (msgs, mr) <- liftIO $ initTcFromModGuts env guts HsSrcFile False m
    let showMsgs (warns, errs) = showSDoc dflags $ vcat
                                                 $    text "Errors:" : pprErrMsgBag errs
                                                   ++ text "Warnings:" : pprErrMsgBag warns
    maybe (fail $ showMsgs msgs) return mr

runDsM :: (HasDynFlags m, HasHermitMEnv m, HasHscEnv m, MonadIO m) => DsM a -> m a
runDsM = runTcM . initDsTc
