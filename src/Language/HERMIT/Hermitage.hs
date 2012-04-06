{-# LANGUAGE RankNTypes, ScopedTypeVariables, FlexibleInstances, KindSignatures, GADTs, DataKinds, TypeOperators #-}

-- A Hermitage is a place of quiet reflection.

module Language.HERMIT.Hermitage (
        Hermitage,
        HermitCmd(..),
        getForeground,
        runHermitCmds
) where

import GhcPlugins

import Control.Monad

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.Types
import Language.HERMIT.KURE


{-
-- CXT is *Kind*.
data CXT where
        Everything :: CXT
        Select :: forall a . a -> CXT -> CXT

We use not-promoted until #5881 is pushed
-}

data Everything = Everything
data Select a b = Select

-- abstact outside this module
data Hermitage :: * -> * -> * where
    HermitageRoot   :: Context a                -> Hermitage Everything a
    Hermitage       :: Context a
                    -> (Rewrite a -> Rewrite b)
                    -> Hermitage cxt b          -> Hermitage (Select b cxt) a

{-
        = Hermitage
        { ageModGuts :: ModGuts
        , ageSelect   :: Select c a
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
               -> CoreM (Either HermitMessage (Hermitage (Select a cxt) x))
focusHermitage zoom h = focus (apply zoomT $ getForeground h)

    where
        zoomT :: Translate a [Context (Generic x)]
        zoomT = rewriteTransformerToTranslate zoom

        focus :: HermitM [Context Blob] -> CoreM (Either HermitMessage (Hermitage (Select a cxt) x))
        focus m = do
                res <- runHermitM m
                case res of
                  -- TODO: complete
                  SuccessR [Context c e] -> case select e of
                                     Nothing -> error "JDGjksdfgh"
                                     Just x  -> return $ Right $ Hermitage (Context c x) zoom h
                  SuccessR [] -> return $ Left $ HermitMessage "no down expressions found"
                  SuccessR xs -> return $ Left $ HermitMessage $ "to many down expressions found: " ++ show (length xs)
                  FailR msg -> return $ Left $ HermitMessage msg
                  YieldR {} -> return $ Left $ TransformationContainedIllegalYield

unfocusHermitage :: Hermitage (Select a cxt) x -> CoreM (Either HermitMessage (Hermitage cxt a))
unfocusHermitage (Hermitage (Context _ a) rrT rest) = applyRewrite (rrT $ constT a) rest

applyRewrite :: forall a cxt
              . Rewrite a
             -> Hermitage cxt a
             -> CoreM (Either HermitMessage (Hermitage cxt a))
applyRewrite rr h = applyRewrite2 (apply rr (getForeground h))
  where
      applyRewrite2 :: HermitM a -> CoreM (Either HermitMessage (Hermitage cxt a))
      applyRewrite2 m  = do
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

------------------------------------------------------------------


handle :: (Monad m) => Either a b -> (b -> m (Either a c)) -> m (Either a c)
handle (Left msg) _ = return $ Left $ msg
handle (Right a)  m = m a

data Hermit :: * -> * where
   Focus :: (Term a, Term x, Generic x ~ Blob) => (Rewrite x -> Rewrite a) -> [ Hermit x ] -> Hermit a
   Apply :: Rewrite a                                                    -> Hermit a

runHermits :: [Hermit a] -> Hermitage cxt a -> CoreM (Either HermitMessage (Hermitage cxt a))
runHermits []         h = return $ Right $ h
runHermits (cmd:cmds) h = do
        ret <- runHermit cmd h
        handle ret $ \ h1 -> runHermits cmds h1

runHermit :: Hermit a -> Hermitage cxt a -> CoreM (Either HermitMessage (Hermitage cxt a))
runHermit (Focus kick inners) h = do
        ret <- focusHermitage kick h
        handle ret $ \ h1 -> do
                ret <- runHermits inners h1
                handle ret $ \ h2 ->
                        unfocusHermitage h2
runHermit (Apply rr) h = applyRewrite rr h

-------------------------------------------------------------------------------

data HermitCmd :: * where
   FocusCmd     :: (Rewrite Blob -> Rewrite Blob)               -> HermitCmd
   PopFocusCmd                                                  :: HermitCmd
   ApplyCmd     :: Rewrite Blob                                 -> HermitCmd

-- The arguments here should be bundled into a datastructure.
-- (except the Hermitage c a, because the polymorphism here would stop simple updates.)

-- The untyped version

runHermitCmds
        :: (forall cxt . Hermitage cxt Blob -> IO HermitCmd)  -- waiting for commands
        -> (String -> IO ())                                    -- where to send errors
        -> ModGuts -> CoreM ModGuts
runHermitCmds getCmd errorMsg modGuts = do
        HermitageRoot (Context _ (ModGutsBlob modGuts')) <- loop (HermitageRoot (Context initHermitEnv (ModGutsBlob modGuts)))
        return modGuts'
 where
    loop :: Hermitage cxt Blob -> CoreM (Hermitage cxt Blob)
    loop h = do
        rep <- liftIO $ getCmd h
        case rep of
           PopFocusCmd -> return h
           FocusCmd kick -> do
                res <- focusHermitage kick h
                case res of
                  Left msg -> do
                     liftIO $ errorMsg $ show msg
                     loop h
                  Right h1 -> do
                       h2 <- loop h1
                       res <- unfocusHermitage h2
                       case res of
                         Left msg -> do
                           -- This was bad, the unfocus failed. Should never happen
                           -- The entire recursive call has been thrown away (back to h)
                           liftIO $ errorMsg $ show msg
                           loop h
                         Right h3 -> do
                           loop h3
           ApplyCmd rr -> do
                res <- applyRewrite rr h
                case res of
                  Left msg -> do
                     liftIO $ errorMsg $ show msg
                     loop h
                  Right h1 -> do
                     loop h1
