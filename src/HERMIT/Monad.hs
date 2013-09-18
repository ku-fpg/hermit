{-# LANGUAGE CPP, InstanceSigs #-}

module HERMIT.Monad
          (
            -- * The HERMIT Monad
            HermitM
          , runHM
          , liftCoreM
          , newGlobalIdH
          , newIdH
          , newTyVarH
          , newCoVarH
          , cloneVarH
            -- * Saving Definitions
          , Label
          , DefStash
          , saveDef
          , lookupDef
          , getStash
            -- * Messages
          , HermitMEnv(..)
          , DebugMessage(..)
          , mkHermitMEnv
          , sendDebugMessage
) where

import Prelude hiding (lookup)

import Data.Map

import Control.Monad
import Control.Monad.IO.Class
import Control.Applicative
import Control.Arrow

import Language.KURE

import HERMIT.Core
import HERMIT.Context
import HERMIT.Kure.SumTypes
import HERMIT.GHC

----------------------------------------------------------------------------

-- | A label for individual definitions.
type Label = String

-- | A store of saved definitions.
type DefStash = Map Label CoreDef

-- | A way of sending messages to top level
newtype HermitMEnv = HermitMEnv { hs_debugChan :: DebugMessage -> HermitM () }

-- | The HERMIT monad is kept abstract.
newtype HermitM a = HermitM (HermitMEnv -> DefStash -> CoreM (KureM (DefStash, a)))

runHermitM :: HermitM a -> HermitMEnv -> DefStash -> CoreM (KureM (DefStash, a))
runHermitM (HermitM f) = f

-- | Eliminator for 'HermitM'.
runHM :: HermitMEnv -> DefStash -> (DefStash -> a -> CoreM b) -> (String -> CoreM b) -> HermitM a -> CoreM b
runHM env s success failure ma = runHermitM ma env s >>= runKureM (\ (a,b) -> success a b) failure

----------------------------------------------------------------------------

-- | Get the stash of saved definitions.
getStash :: HermitM DefStash
getStash = HermitM (\ _ s -> return $ return (s, s))

-- | Replace the stash of saved definitions.
putStash :: DefStash -> HermitM ()
putStash s = HermitM (\ _ _ -> return $ return (s, ()))

sendDebugMessage :: DebugMessage -> HermitM ()
sendDebugMessage msg = do env <- HermitM $ \ ch s -> return $ return (s, ch)
                          hs_debugChan env msg

-- | Save a definition for future use.
saveDef :: Label -> CoreDef -> HermitM ()
saveDef l d = getStash >>= (insert l d >>> putStash)

-- | Lookup a previously saved definition.
lookupDef :: Label -> HermitM CoreDef
lookupDef l = getStash >>= (lookup l >>> maybe (fail "Definition not found.") return)

----------------------------------------------------------------------------

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
  return a = HermitM $ \ _ s -> return (return (s,a))

  (>>=) :: HermitM a -> (a -> HermitM b) -> HermitM b
  (HermitM gcm) >>= f = HermitM $ \ env -> gcm env >=> runKureM (\ (s', a) -> runHermitM (f a) env s') (return . fail)

  fail :: String -> HermitM a
  fail msg = HermitM $ \ _ _ -> return (fail msg)

instance MonadCatch HermitM where
  catchM :: HermitM a -> (String -> HermitM a) -> HermitM a
  (HermitM gcm) `catchM` f = HermitM $ \ env s -> gcm env s >>= runKureM (return.return) (\ msg -> runHermitM (f msg) env s)

----------------------------------------------------------------------------

-- | 'CoreM' can be lifted to 'HermitM'.
liftCoreM :: CoreM a -> HermitM a
liftCoreM ma = HermitM $ \ _ s -> do a <- ma
                                     return (return (s,a))

instance MonadIO HermitM where
  liftIO :: IO a -> HermitM a
  liftIO = liftCoreM . liftIO

instance MonadUnique HermitM where
  getUniqueSupplyM :: HermitM UniqSupply
  getUniqueSupplyM = liftCoreM getUniqueSupplyM

instance MonadThings HermitM where
  lookupThing :: Name -> HermitM TyThing
  lookupThing = liftCoreM . lookupThing

instance HasDynFlags HermitM where
  getDynFlags :: HermitM DynFlags
  getDynFlags = liftCoreM getDynFlags

----------------------------------------------------------------------------

newName :: String -> HermitM Name
newName nm = mkSystemVarName <$> getUniqueM <*> pure (mkFastString nm)

-- | Make a unique global identifier for a specified type, using a provided name.
newGlobalIdH :: String -> Type -> HermitM Id
newGlobalIdH nm ty = mkVanillaGlobal <$> newName nm <*> pure ty

-- | Make a unique identifier for a specified type, using a provided name.
newIdH :: String -> Type -> HermitM Id
newIdH nm ty = mkLocalId <$> newName nm <*> pure ty

-- | Make a unique type variable for a specified kind, using a provided name.
newTyVarH :: String -> Kind -> HermitM TyVar
newTyVarH nm k = mkTyVar <$> newName nm <*> pure k

-- | Make a unique coercion variable for a specified type, using a provided name.
newCoVarH :: String -> Type -> HermitM TyVar
newCoVarH nm ty = mkCoVar <$> newName nm <*> pure ty

-- | Make a new variable of the same type, with a modified textual name.
cloneVarH :: (String -> String) -> Var -> HermitM Var
cloneVarH nameMod v | isTyVar v = newTyVarH name ty
                    | isCoVar v = newCoVarH name ty
                    | isId v    = newIdH name ty
                    | otherwise = fail "If this variable isn't a type, coercion or identifier, then what is it?"
  where
    name = nameMod (uqName v)
    ty   = varType v

----------------------------------------------------------------------------

-- | A message packet.
data DebugMessage = DebugTick String
                  | DebugCore String HermitC CoreTC

mkHermitMEnv :: (DebugMessage -> HermitM ()) -> HermitMEnv
mkHermitMEnv debugger = HermitMEnv { hs_debugChan = debugger }

----------------------------------------------------------------------------
