{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE StandaloneDeriving #-}

module HERMIT.Monad
    ( -- * The HERMIT Monad
      HermitM
    , runHM
    , embedHermitM
    , HermitMEnv
    , HermitMResult(..)
    , LiftCoreM(..)
    , getHscEnv
    , runTcM
    , runDsM
      -- * Lemmas
    , HasLemmas(..)
    , addLemma
    , findLemma
    , insertLemma
    , deleteLemma
      -- * Reader Information
    , HasHermitMEnv(..)
    , mkEnv
    , getModGuts
      -- * Messages
    , getDebugChan
    , KEnvMessage(..)
    , sendKEnvMessage
    ) where

import Prelude.Compat hiding (lookup)

import Control.Monad (when) -- Needs to have Monad context on GHC 7.8
import Control.Monad.Compat hiding (when)
import Control.Monad.IO.Class

import Data.Map
import Data.Typeable

import Language.KURE

import HERMIT.Core
import HERMIT.Context
import HERMIT.GHC
import HERMIT.GHC.Typechecker
import HERMIT.Kure.Universes
import HERMIT.Lemma

----------------------------------------------------------------------------

-- | The HermitM environment.
data HermitMEnv = HermitMEnv { hEnvChanged   :: Bool -- ^ Whether Lemmas have changed
                             , hEnvDebug     :: DebugChan
                             , hEnvModGuts   :: ModGuts -- ^ Note: this is a snapshot of the ModGuts from
                                                        --         before the current transformation.
                             , hEnvLemmas    :: Lemmas
                             } deriving Typeable

type DebugChan = KEnvMessage -> HermitM ()

mkEnv :: DebugChan -> ModGuts -> Lemmas -> HermitMEnv
mkEnv = HermitMEnv False

-- | The HermitM result record.
data HermitMResult a = HermitMResult { hResChanged :: Bool -- ^ Whether Lemmas have changed
                                     , hResLemmas :: Lemmas
                                     , hResult    :: a
                                     } deriving Typeable

changedResult :: Lemmas -> a -> HermitMResult a
changedResult = HermitMResult True

-- Does not change the Changed status of Lemmas
mkResult :: HermitMEnv -> a -> HermitMResult a
mkResult env = HermitMResult (hEnvChanged env) (hEnvLemmas env)

-- | The HERMIT monad is kept abstract.
--
-- It provides a reader for ModGuts, state for Lemmas,
-- and access to a debugging channel.
newtype HermitM a = HermitM { runHermitM :: HermitMEnv -> CoreM (KureM (HermitMResult a)) }
  deriving Typeable

-- | Eliminator for 'HermitM'.
runHM :: HermitMEnv                    -- env
      -> (HermitMResult a -> CoreM b)  -- success
      -> (String -> CoreM b)           -- failure
      -> HermitM a                     -- ma
      -> CoreM b
runHM env success failure ma = runHermitM ma env >>= runKureM success failure

-- | Allow HermitM to be embedded in another monad with proper capabilities.
embedHermitM :: (HasHermitMEnv m, HasLemmas m, LiftCoreM m) => HermitM a -> m a
embedHermitM hm = do
    env <- getHermitMEnv
    r <- liftCoreM (runHermitM hm env) >>= runKureM return fail
    when (hResChanged r) $ forM_ (toList (hResLemmas r)) $ uncurry insertLemma
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
  return a = HermitM $ \ env -> return (return (mkResult env a))

  (>>=) :: HermitM a -> (a -> HermitM b) -> HermitM b
  (HermitM gcm) >>= f =
        HermitM $ \ env -> gcm env >>= runKureM (\ (HermitMResult c ls a) ->
                                                        let env' = env { hEnvChanged = c, hEnvLemmas = ls }
                                                        in  runHermitM (f a) env')
                                                (return . fail)

  fail :: String -> HermitM a
  fail msg = HermitM $ const $ return $ fail msg

instance MonadCatch HermitM where
  catchM :: HermitM a -> (String -> HermitM a) -> HermitM a
  (HermitM gcm) `catchM` f = HermitM $ \ env -> gcm env >>= runKureM (return.return)
                                                                     (\ msg -> runHermitM (f msg) env)

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

deriving instance Typeable HasHermitMEnv

instance HasHermitMEnv HermitM where
    getHermitMEnv = HermitM $ \ env -> return $ return $ mkResult env env

getModGuts :: (HasHermitMEnv m, Monad m) => m ModGuts
getModGuts = liftM hEnvModGuts getHermitMEnv

----------------------------------------------------------------------------

getDebugChan :: (HasHermitMEnv m, Monad m) => m DebugChan
getDebugChan = liftM hEnvDebug getHermitMEnv

sendKEnvMessage :: (HasHermitMEnv m, HasLemmas m, LiftCoreM m) => KEnvMessage -> m ()
sendKEnvMessage msg = getDebugChan >>= embedHermitM . ($ msg)

----------------------------------------------------------------------------

class HasLemmas m where
    getLemmas :: m Lemmas
    putLemmas :: Lemmas -> m ()

deriving instance Typeable HasLemmas

instance HasLemmas HermitM where
    getLemmas = HermitM $ \ env -> return $ return $ mkResult env (hEnvLemmas env)
    putLemmas m = HermitM $ \ _ -> return $ return $ changedResult m ()

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

deleteLemma :: (HasLemmas m, Monad m) => LemmaName -> m ()
deleteLemma nm = getLemmas >>= putLemmas . delete nm

----------------------------------------------------------------------------

class Monad m => LiftCoreM m where
    -- | 'CoreM' can be lifted to this monad.
    liftCoreM :: CoreM a -> m a

deriving instance Typeable LiftCoreM

instance LiftCoreM HermitM where
    liftCoreM coreM = HermitM $ \ env -> coreM >>= return . return . mkResult env

getHscEnv :: LiftCoreM m => m HscEnv
getHscEnv = liftCoreM getHscEnvCoreM

----------------------------------------------------------------------------

-- | A message packet.
data KEnvMessage :: * where
    DebugTick :: String -> KEnvMessage
    DebugCore :: (LemmaContext c, ReadBindings c, ReadPath c Crumb) => String -> c -> LCoreTC -> KEnvMessage
    AddObligation :: HermitC -> LemmaName -> Lemma -> KEnvMessage -- obligation that must be proven
  deriving Typeable

----------------------------------------------------------------------------

runTcM :: (HasDynFlags m, HasHermitMEnv m, LiftCoreM m, MonadIO m) => TcM a -> m a
runTcM m = do
    env <- getHscEnv
    dflags <- getDynFlags
    guts <- getModGuts
    -- What is the effect of HsSrcFile (should we be using something else?)
    -- What should the boolean flag be set to?
    (msgs, mr) <- liftIO $ initTcFromModGuts env guts HsSrcFile False m
    let showMsgs (warns, errs) = showSDoc dflags $ vcat
                                                 $    text "Errors:" : pprErrMsgBagWithLoc errs
                                                   ++ text "Warnings:" : pprErrMsgBagWithLoc warns
    maybe (fail $ showMsgs msgs) return mr

runDsM :: (HasDynFlags m, HasHermitMEnv m, LiftCoreM m, MonadIO m) => DsM a -> m a
runDsM = runTcM . initDsTc
