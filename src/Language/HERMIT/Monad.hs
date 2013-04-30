{-# LANGUAGE InstanceSigs #-}

module Language.HERMIT.Monad
          (
            -- * The HERMIT Monad
            HermitM
          , runHM
          , liftCoreM
          , newIdH
          , newTyVarH
    --      , newVarExprH
    --      , newVarH
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

import GhcPlugins hiding (empty)
import MonadUtils       -- from GHC

import Control.Monad
import Control.Arrow

import Language.KURE

import Language.HERMIT.Core
import Language.HERMIT.Context

----------------------------------------------------------------------------

-- | A label for individual defintions.
type Label = String

-- | A store of saved definitions.
type DefStash = Map Label CoreDef

-- | A way of sending messages to top level
newtype HermitMEnv = HermitMEnv { hs_debugChan :: DebugMessage -> HermitM () }

-- | The HERMIT monad is kept abstract.
newtype HermitM a = HermitM (HermitMEnv -> DefStash -> CoreM (KureM (DefStash, a)))

runHermitM :: HermitM a -> HermitMEnv -> DefStash -> CoreM (KureM (DefStash, a))
runHermitM (HermitM f) = f
{-# INLINE runHermitM #-}

-- | Get the stash of saved definitions.
getStash :: HermitM DefStash
getStash = HermitM (\ _ s -> return $ return (s, s))
{-# INLINE getStash #-}

-- | Replace the stash of saved definitions.
putStash :: DefStash -> HermitM ()
putStash s = HermitM (\ _ _ -> return $ return (s, ()))
{-# INLINE putStash #-}

sendDebugMessage :: DebugMessage -> HermitM ()
sendDebugMessage msg = do env <- HermitM $ \ ch s -> return $ return (s, ch)
                          hs_debugChan env msg
{-# INLINE sendDebugMessage #-}

-- | Save a definition for future use.
saveDef :: Label -> CoreDef -> HermitM ()
saveDef l d = getStash >>= (insert l d >>> putStash)
{-# INLINE saveDef #-}

-- | Lookup a previously saved definition.
lookupDef :: Label -> HermitM CoreDef
lookupDef l = getStash >>= (lookup l >>> maybe (fail "Definition not found.") return)
{-# INLINE lookupDef #-}

-- | Eliminator for 'HermitM'.
runHM :: HermitMEnv -> DefStash -> (DefStash -> a -> CoreM b) -> (String -> CoreM b) -> HermitM a -> CoreM b
runHM env s success failure ma = runHermitM ma env s >>= runKureM (\ (a,b) -> success a b) failure
{-# INLINE runHM #-}

----------------------------------------------------------------------------

instance Functor HermitM where
  fmap :: (a -> b) -> HermitM a -> HermitM b
  fmap = liftM
  {-# INLINE fmap #-}

instance Applicative HermitM where
  pure :: a -> HermitM a
  pure = return
  {-# INLINE pure #-}

  (<*>) :: HermitM (a -> b) -> HermitM a -> HermitM b
  (<*>) = ap
  {-# INLINE (<*>) #-}

instance Monad HermitM where
  return :: a -> HermitM a
  return a = HermitM $ \ _ s -> return (return (s,a))
  {-# INLINE return #-}

  (>>=) :: HermitM a -> (a -> HermitM b) -> HermitM b
  (HermitM gcm) >>= f = HermitM $ \ env -> gcm env >=> runKureM (\ (s', a) -> runHermitM (f a) env s') (return . fail)
  {-# INLINE (>>=) #-}

  fail :: String -> HermitM a
  fail msg = HermitM $ \ _ _ -> return (fail msg)
  {-# INLINE fail #-}

instance MonadCatch HermitM where
  catchM :: HermitM a -> (String -> HermitM a) -> HermitM a
  (HermitM gcm) `catchM` f = HermitM $ \ env s -> gcm env s >>= runKureM (return.return) (\ msg -> runHermitM (f msg) env s)
  {-# INLINE catchM #-}

----------------------------------------------------------------------------

-- | 'CoreM' can be lifted to 'HermitM'.
liftCoreM :: CoreM a -> HermitM a
liftCoreM ma = HermitM $ \ _ s -> do a <- ma
                                     return (return (s,a))
{-# INLINE liftCoreM #-}

instance MonadIO HermitM where
  liftIO :: IO a -> HermitM a
  liftIO = liftCoreM . liftIO
  {-# INLINE liftIO #-}

instance MonadUnique HermitM where
  getUniqueSupplyM :: HermitM UniqSupply
  getUniqueSupplyM = liftCoreM getUniqueSupplyM
  {-# INLINE getUniqueSupplyM #-}

instance MonadThings HermitM where
  lookupThing :: Name -> HermitM TyThing
  lookupThing = liftCoreM . lookupThing
  {-# INLINE lookupThing #-}

instance HasDynFlags HermitM where
  getDynFlags :: HermitM DynFlags
  getDynFlags = liftCoreM getDynFlags
  {-# INLINE getDynFlags #-}

----------------------------------------------------------------------------

newName :: String -> HermitM Name
newName name = do uq <- getUniqueM
                  return $ mkSystemVarName uq $ mkFastString name
{-# INLINE newName #-}

-- | Make a unique identifier for a specified type based on a provided name.
newIdH :: String -> Type -> HermitM Id
newIdH name ty = do name' <- newName name
                    return $ mkLocalId name' ty
{-# INLINE newIdH #-}

-- | Make a unique type variable for a specified kind based on a provided name.
newTyVarH :: String -> Kind -> HermitM TyVar
newTyVarH name kind = do name' <- newName name
                         return $ mkTyVar name' kind
{-# INLINE newTyVarH #-}

-- | This gives an new version of a 'Var', with the same info, and a new textual name.
cloneVarH :: (String -> String) -> Var -> HermitM Var
cloneVarH nameMod v =
        let name = nameMod (getOccString v)
            ty   = varType v
        in
          if isTyVar v
           then newTyVarH name ty
           else newIdH name ty
{-# INLINE cloneVarH #-}

----------------------------------------------------------------------------

-- | A message packet.
data DebugMessage  =  DebugTick String
                   |  DebugCore String HermitC Core    -- ^ A postcard.

mkHermitMEnv :: (DebugMessage -> HermitM ()) -> HermitMEnv
mkHermitMEnv debugger = HermitMEnv
                { hs_debugChan = debugger
                }
{-# INLINE mkHermitMEnv #-}

----------------------------------------------------------------------------
