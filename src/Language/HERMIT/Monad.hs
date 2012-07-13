{-# LANGUAGE TupleSections #-}

module Language.HERMIT.Monad
          (
            -- * The HERMIT Monad
            HermitM
          , runHM
          , liftCoreM
          , newVarH
            -- * Saving Definitions
          , Label
          , DefStash
          , saveDef
          , lookupDef
) where

import Prelude hiding (lookup)

import Data.Map

import GhcPlugins hiding (empty)
import MonadUtils       -- from GHC

import Control.Monad

import Language.KURE.Combinators
import Language.KURE.Utilities

import Language.HERMIT.CoreExtra

import qualified Language.Haskell.TH as TH

----------------------------------------------------------------------------

-- | A label for individual defintions.
type Label = String

-- | A store of saved definitions.
type DefStash = Map Label CoreDef

-- | The HERMIT monad is kept abstract.
newtype HermitM a = HermitM (DefStash -> CoreM (KureMonad (DefStash, a)))

runHermitM :: HermitM a -> DefStash -> CoreM (KureMonad (DefStash, a))
runHermitM (HermitM f) = f

getStash :: HermitM DefStash
getStash = HermitM (\ s -> return $ return (s, s))

putStash :: DefStash -> HermitM ()
putStash s = HermitM (\ _ -> return $ return (s, ()))

-- | Save a definition for future use.
saveDef :: Label -> CoreDef -> HermitM ()
saveDef l d = do s <- getStash
                 putStash (insert l d s)

-- | Lookup a previously saved definition.
lookupDef :: Label -> HermitM CoreDef
lookupDef l = do s <- getStash
                 maybe (fail "Definition not found.") return (lookup l s)

-- | Eliminator for 'HermitM'.
runHM :: DefStash -> (DefStash -> a -> CoreM b) -> (String -> CoreM b) -> HermitM a -> CoreM b
runHM s success failure ma = runHermitM ma s >>= runKureMonad (uncurry success) failure

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
   return a = HermitM $ \ s -> return (return (s,a))

-- (>>=) :: HermitM a -> (a -> HermitM b) -> HermitM b
   (HermitM gcm) >>= f = HermitM $ gcm >=> runKureMonad (\ (s', a) -> runHermitM (f a) s') (return . fail)

-- fail :: String -> HermitM a
   fail msg = HermitM $ \ _ -> return (fail msg)

instance MonadCatch HermitM where
-- catchM :: HermitM a -> (String -> HermitM a) -> HermitM a
   (HermitM gcm) `catchM` f = HermitM $ \ s -> gcm s >>= runKureMonad (return.return) (\ msg -> runHermitM (f msg) s)

----------------------------------------------------------------------------

-- | 'CoreM' can be lifted to 'HermitM'.
liftCoreM :: CoreM a -> HermitM a
liftCoreM ma = HermitM $ \ s -> do a <- ma
                                   return (return (s,a))

instance MonadIO HermitM where
   liftIO = liftCoreM . liftIO

instance MonadUnique HermitM where
   getUniqueSupplyM = liftCoreM getUniqueSupplyM

----------------------------------------------------------------------------

-- | Make a unique 'Id' for a specified type based on a provided 'TH.Name'.
newVarH :: TH.Name -> Type -> HermitM Id
newVarH nm ty = do uq <- getUniqueM
                   let fast_str = mkFastString (show nm)
                       name     = mkSystemVarName uq fast_str
                   return (mkLocalId name ty)

-- newTypeVarH :: TH.Name -> Kind -> HermitM TyVar
-- newTypeVarH = undefined -- TO DO!

----------------------------------------------------------------------------
