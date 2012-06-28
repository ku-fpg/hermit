module Language.HERMIT.Monad
          (
            -- * The HERMIT Monad
            HermitM
          , runHM
          , liftCoreM
          , newVarH
) where

import GhcPlugins hiding (empty)
import MonadUtils       -- from GHC

import Control.Applicative

import Language.KURE.Combinators
import Language.KURE.Utilities

import qualified Language.Haskell.TH as TH

----------------------------------------------------------------------------

-- | The HERMIT monad is kept abstract.
newtype HermitM a = HermitM {runHermitM :: CoreM (KureMonad a)}

-- | Eliminator for 'HermitM'.
runHM :: (a -> CoreM b) -> (String -> CoreM b) -> HermitM a -> CoreM b
runHM s f ma = runHermitM ma >>= runKureMonad s f

----------------------------------------------------------------------------

instance Functor HermitM where
  fmap f (HermitM mha) = HermitM ((fmap.fmap) f mha)

instance Applicative HermitM where
  pure  = HermitM . pure . pure
  (HermitM f) <*> (HermitM a) = HermitM (liftA2 (<*>) f a)

instance Monad HermitM where
  return = pure
  (HermitM mra) >>= f = HermitM (mra >>= runKureMonad (runHermitM.f) (return.fail))
  fail = HermitM . return . fail

instance MonadCatch HermitM where
  (HermitM mra) `catchM` f = HermitM (mra >>= runKureMonad (return.return) (runHermitM.f))

----------------------------------------------------------------------------

-- | 'CoreM' can be lifted to 'HermitM'.
liftCoreM :: CoreM a -> HermitM a
liftCoreM m = HermitM (return <$> m)

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
