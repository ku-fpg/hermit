{-# LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleInstances, KindSignatures, GADTs, DataKinds, TypeOperators #-}

-- A Hermitage is a place of quiet reflection.

module Language.HERMIT.Hermitage where

import GhcPlugins

import Control.Monad

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.Types
import Language.HERMIT.KURE



-- CXT is *Kind*.
data CXT where
        Everything :: CXT
        (:<) :: a -> CXT -> CXT


-- abstact outside this module
data Hermitage :: CXT -> * -> * where
    HermitageRoot   :: Context ModGuts          -> Hermitage Everything ModGuts
    Hermitage       :: Context a
                    -> (Rewrite a -> Rewrite b)
                    -> Hermitage cxt b          -> Hermitage (b :< cxt) a

{-
        = Hermitage
        { ageModGuts :: ModGuts
        , ageFocus   :: Focus c a
        , ageEnv     :: HermitEnv
        }
-}
-- Create a new Hermitage, does not return until the interaction
-- is completed.
new :: (Hermitage Everything ModGuts -> CoreM (Hermitage Everything ModGuts)) -> ModGuts -> CoreM ModGuts
new k modGuts = do
        HermitageRoot (Context _ modGuts') <- k (HermitageRoot (Context initHermitEnv modGuts))
        return modGuts'
{-

-- | What are the *current* module guts?
getModGuts :: Hermitage cxt a -> ModGuts
getModGuts age = ageModGuts age

-}
-- | 'getForeground' gets the current 'blob' under consideraton.
getForeground :: Hermitage cxt a -> Context a
getForeground (HermitageRoot a) = a
getForeground (Hermitage a _ _) = a

-- | 'getBackground' gets the current context of the blob under consideraton.
getBackground :: Hermitage cxt a -> (a -> Hermitage cxt a)
getBackground (HermitageRoot (Context c _))      a = HermitageRoot (Context c a)
getBackground (Hermitage (Context c _) hrr rest) a = Hermitage (Context c a) hrr rest


-- this focuses in to a sub-expresssion. It will do error checking, hence the
-- need for the the CoreM.

focusHermitage :: forall x a cxt
                . (Term x, Generic x ~ Blob)
               => (Rewrite x -> Rewrite a)
               -> Hermitage cxt a
               -> CoreM (Either HermitMessage (Hermitage (a :< cxt) x))
focusHermitage zoom h = focus (apply zoomT $ getForeground h)

    where
        zoomT :: Translate a [Context (Generic x)]
        zoomT = rewriteTransformerToTranslate zoom

        focus :: HermitM [Context Blob] -> CoreM (Either HermitMessage (Hermitage (a :< cxt) x))
        focus m = do
                res <- runHermitM m
                case res of
                  -- TODO: complete
                  SuccessR [Context c e] -> case select e of
                                     Nothing -> error "JDGjksdfgh"
                                     Just x  -> return $ Right $ Hermitage (Context c x) zoom h

unfocusHermitage :: Hermitage (a :< cxt) x -> CoreM (Either HermitMessage (Hermitage cxt a))
unfocusHermitage (Hermitage (Context _ a) rrT rest) = applyRewrite (rrT $ constT a) rest

applyRewrite :: forall a cxt
              . Rewrite a
             -> Hermitage cxt a
             -> CoreM (Either HermitMessage (Hermitage cxt a))
applyRewrite rr h = applyRewrite2 (getBackground h) (apply rr (getForeground h))
  where
      applyRewrite2 :: (a -> Hermitage cxt a) -> HermitM a -> CoreM (Either HermitMessage (Hermitage cxt a))
      applyRewrite2  cons m  = do
              r <- runHermitM m
              case r of
                SuccessR a -> return $ Right (getBackground h a)
                FailR msg  -> return $ Left $ HermitMessage msg
                YieldR {}  -> return $ Left $ TransformationContainedIllegalYield

------------------------------------------------------------------


data HermitMessage
        = UnableToFocusMessage
        | TransformationContainedIllegalYield
        | HermitMessage String
        deriving (Show)

