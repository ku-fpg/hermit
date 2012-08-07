{-# LANGUAGE TupleSections, GADTs, KindSignatures #-}

module Language.HERMIT.Monad
          (
            -- * The HERMIT Monad
            HermitM
          , runHM
          , liftCoreM
          , newVarH
          , newTypeVarH
            -- * Saving Definitions
          , Label
          , DefStash
          , saveDef
          , lookupDef
          , getStash
          , HermitMEnv(..)
          , DebugMessage(..)
          , mkHermitMEnv
          , sendDebugMessage
) where

import Prelude hiding (lookup)

import Data.Map

import GhcPlugins hiding (empty)
import MonadUtils       -- from GHC

import Control.Monad
import Control.Arrow

import Language.KURE.Combinators
import Language.KURE.Utilities

import Language.HERMIT.CoreExtra
import Language.HERMIT.Context

----------------------------------------------------------------------------

-- | A label for individual defintions.
type Label = String

-- | A store of saved definitions.
type DefStash = Map Label CoreDef

-- | A way of sending messages to top level
newtype HermitMEnv = HermitMEnv { hs_debugChan :: DebugMessage -> HermitM () }

-- | The HERMIT monad is kept abstract.
newtype HermitM a = HermitM (HermitMEnv -> DefStash -> CoreM (KureMonad (DefStash, a)))

runHermitM :: HermitM a -> HermitMEnv -> DefStash -> CoreM (KureMonad (DefStash, a))
runHermitM (HermitM f) = f

getStash :: HermitM DefStash
getStash = HermitM (\ _ s -> return $ return (s, s))

putStash :: DefStash -> HermitM ()
putStash s = HermitM (\ _ _ -> return $ return (s, ()))

sendDebugMessage :: DebugMessage -> HermitM ()
sendDebugMessage msg =
        do env <- HermitM $ \ ch s -> return $ return (s, ch)
           hs_debugChan env msg

-- | Save a definition for future use.
saveDef :: Label -> CoreDef -> HermitM ()
saveDef l d = getStash >>= (insert l d >>> putStash)

-- | Lookup a previously saved definition.
lookupDef :: Label -> HermitM CoreDef
lookupDef l = getStash >>= (lookup l >>> maybe (fail "Definition not found.") return)

-- | Eliminator for 'HermitM'.
runHM :: HermitMEnv -> DefStash -> (DefStash -> a -> CoreM b) -> (String -> CoreM b) -> HermitM a -> CoreM b
runHM env s success failure ma = runHermitM ma env s >>= runKureMonad (\ (a,b) -> success a b) failure

----------------------------------------------------------------------------

instance Functor HermitM where
-- fmap :: (a -> b) -> HermitM a -> HermitM b
   fmap = liftM

instance Applicative HermitM where
-- pure :: a -> HermitM a
   pure  = return

-- (<*>) :: HermitM (a -> b) -> HermitM a -> HermitM b
   (<*>) = ap

instance Monad HermitM where
-- return :: a -> HermitM a
   return a = HermitM $ \ _ s -> return (return (s,a))

-- (>>=) :: HermitM a -> (a -> HermitM b) -> HermitM b
   (HermitM gcm) >>= f = HermitM $ \ env -> gcm env >=> runKureMonad (\ (s', a) -> runHermitM (f a) env s') (return . fail)

-- fail :: String -> HermitM a
   fail msg = HermitM $ \ _ _ -> return (fail msg)

instance MonadCatch HermitM where
-- catchM :: HermitM a -> (String -> HermitM a) -> HermitM a
   (HermitM gcm) `catchM` f = HermitM $ \ env s -> gcm env s >>= runKureMonad (return.return) (\ msg -> runHermitM (f msg) env s)

----------------------------------------------------------------------------

-- | 'CoreM' can be lifted to 'HermitM'.
liftCoreM :: CoreM a -> HermitM a
liftCoreM ma = HermitM $ \ _ s -> do a <- ma
                                     return (return (s,a))

instance MonadIO HermitM where
   liftIO = liftCoreM . liftIO

instance MonadUnique HermitM where
   getUniqueSupplyM = liftCoreM getUniqueSupplyM

instance MonadThings HermitM where
   lookupThing = liftCoreM . lookupThing

----------------------------------------------------------------------------

newName :: String -> HermitM Name
newName nm = flip mkSystemVarName (mkFastString nm) <$> getUniqueM

-- | Make a unique identifier for a specified type based on a provided name.
newVarH :: String -> Type -> HermitM Id
newVarH nm ty = flip mkLocalId ty <$> newName nm

-- | Make a unique type variable for a specified kind based on a provided name.
newTypeVarH :: String -> Kind -> HermitM TyVar
newTypeVarH nm kind = flip mkTyVar kind <$> newName nm

----------------------------------------------------------------------------

-- | A message packet.
data DebugMessage :: * where
        DebugTick    :: String                    -> DebugMessage
        DebugCore    :: String -> Context -> Core -> DebugMessage       -- A postcard

mkHermitMEnv :: (DebugMessage -> HermitM ()) -> HermitMEnv
mkHermitMEnv debugger = HermitMEnv
                { hs_debugChan = debugger
                }
