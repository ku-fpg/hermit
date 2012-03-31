{-# LANGUAGE TypeFamilies, FlexibleInstances, FlexibleContexts, GADTs #-}

module Language.HERMIT.Types where

import GhcPlugins
import qualified Data.Map as Map
import Data.Monoid

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad

import qualified Control.Category as Cat
import Control.Arrow
import Control.Monad

----------------------------------------------------------------------------
-- The transformation/HERMIT monad
newtype HermitM a = HermitM { runHermitM :: CoreM (HermitR a) }

data HermitR :: * -> * where
        SuccessR :: a                   -> HermitR a
        FailR    :: String               -> HermitR a
        YieldR   :: a  -> [Context Blob] -> HermitR a

instance Monad HermitM where
        return a = HermitM (return $ SuccessR a)
        (HermitM m) >>= k = HermitM $ do
                r <- m
                case r of
                  SuccessR a -> runHermitM (k a)
                  FailR msg  -> return $ FailR msg
                  YieldR a c1 -> do
                           r' <- runHermitM (k a)
                           case r' of
                             SuccessR a  -> return $ SuccessR a
                             FailR msg   -> return $ FailR msg
                             YieldR a c2 -> return $ YieldR a (c1 ++ c2)
        fail msg = HermitM (return $ FailR msg)

yieldM :: Context Blob -> HermitM ()
yieldM blob = HermitM $ return $ YieldR () [blob]

catchH :: HermitM a -> (String -> HermitM a) -> HermitM a
catchH (HermitM m) k = HermitM $ do
        r <- m
        case r of
          SuccessR a -> return $ SuccessR a
          FailR msg  -> runHermitM (k msg)
          YieldR a c -> return $ YieldR a c

----------------------------------------------------------------------------
{-
runHermitM :: HermitM a -> CoreM (Either String a)
runHermitM (HermitM m) = liftM Right m
runHermitM (FailM str) = return $ Left str
-}
----------------------------------------------------------------------------

-- | Our unit of operation and key type, a 'Translate'.
newtype HermitT exp1 exp2 = HermitT (exp1 -> HermitM exp2)

-- | 'apply' directly applies a 'Translate' value to an argument.
apply :: HermitT exp1 exp2 -> exp1 -> HermitM exp2
apply (HermitT t) exp1 = t exp1

instance Cat.Category HermitT where
   id = HermitT $ \  e -> return e
   (.) rr1 rr2 = HermitT $ \ e -> apply rr2 e >>= apply rr1

instance Arrow HermitT where
   arr f = HermitT (\ e -> return (f e))
   first rr = HermitT $ \ (b,d) -> do e <- apply rr b ; return (e,d)

----------------------------------------------------------------------------
-- TODO: figure this out, we use it quite a bit
type Translate exp1 exp2 = HermitT (Context exp1) exp2

-- | 'translate' is the standard way of building a 'Translate'.
translate :: (Context exp1 -> HermitM exp2) -> Translate exp1 exp2
translate = HermitT


----------------------------------------------------------------------------
-- Type synonym for endomorphic translation of values *with context* on the input.
type Rewrite exp = Translate exp exp

-- | 'rewrite' is our primitive way of building a Rewrite,
--
-- @rewrite $ \\ _ e -> return e@ /is/ (now) an identity rewrite.

rewrite :: (Context exp -> HermitM exp) -> Rewrite exp
rewrite f = translate f

---------------------------------------------------------------------

data Context exp = Context HermitEnv exp

instance Functor Context where
        fmap f (Context env e) = Context env (f e)

---------------------------------------------------------------------

class (Generic exp ~ Generic (Generic exp)) => Term exp where
  -- | 'Generic' is a sum of all the interesting sub-types, transitively, of @exp@.
  -- We use @Generic e ~ e@ to signify that something is its own Generic.
  -- Simple expression types might be their own sole 'Generic', more complex examples
  -- will have a new datatype for the 'Generic', which will also be an instance of class 'Term'.
  type Generic exp

  -- | 'select' looks in a 'Generic', to get the exp inside, or fails.
  select :: Generic exp -> Maybe exp

  -- | 'inject' injects an exp into a 'Generic'.
  inject :: exp -> Generic exp

  -- | 'allR' applies 'Generic' rewrites to all the (interesting) children of this node.
  allR :: Rewrite (Generic exp) -> Rewrite exp

  -- | 'crushU' applies a 'Generic' Translate to a common, 'Monoid'al result, to all the interesting children of this node.
  crushU :: (Monoid result) => Translate (Generic exp) result -> Translate exp result

---------------------------------------------------------------------

-- | 'extractR' converts a 'Rewrite' over a 'Generic' into a rewrite over a specific expression type.
extractR  :: (Term exp) => Rewrite (Generic exp) -> Rewrite exp	-- at *this* type
extractR rr = rewrite $ \ cxt -> do
            e' <- apply rr (fmap inject cxt)
            case select e' of
                Nothing -> fail "extractR"
                Just r -> return r

-- | 'extractU' converts a 'Translate' taking a 'Generic' into a translate over a specific expression type.
extractU  :: (Term exp) => Translate (Generic exp) r -> Translate exp r
extractU rr = translate $ apply rr . fmap inject

-- | 'promoteR' promotes a 'Rewrite' into a 'Generic' 'Rewrite'; other types inside Generic cause failure.
-- 'try' can be used to convert a failure-by-default promotion into a 'id-by-default' promotion.
promoteR  :: (Term exp) => Rewrite  exp -> Rewrite  (Generic exp)
promoteR rr = rewrite $ \ (Context c e) -> do
               case select e of
                 Nothing -> fail "promoteR"
                 Just e' -> do
                    r <- apply rr (Context c e')
                    return (inject r)

-- | 'promoteU' promotes a 'Translate' into a 'Generic' 'Translate'; other types inside Generic cause failure.
promoteU  :: (Term exp) => Translate  exp r -> Translate  (Generic exp) r
promoteU rr = translate $ \ (Context c e) -> do
               case select e of
                 Nothing -> fail "promoteI"
                 Just e' -> apply rr (Context c e')

----------------------------------------------------------------------------


-- To rename
data Blob
        = ModGutsBlob   ModGuts
        | BindBlob      (Bind Id)
        | ExprBlob      (Expr Id)
        | TypeBlob      Type


instance Term Blob where
  type Generic Blob = Blob

  select _ = Nothing
  inject   = id

instance Term ModGuts where
  type Generic ModGuts = Blob

  select (ModGutsBlob guts) = return guts
  select _              = Nothing
  inject                = ModGutsBlob



instance Term (Bind Id) where
  type Generic (Bind Id) = Blob
--  data Context (Bind Id) = BindBlobContext (Bind Id)

  select (BindBlob expr) = return expr
  select _              = Nothing
  inject                = BindBlob

  allR rr = rewrite $ \ (Context c e) -> case e of
          NonRec n e1 -> do
                   e1' <- apply (extractR rr) (Context c e1)
                   return $ NonRec n e1'
          Rec bds -> do
                  -- Notice how we add the scoping bindings
                  -- here *before* decending into the rhss.
                   let env' = addHermitBinding (Rec bds) c
                   bds' <- sequence
                        [ do e' <- apply (extractR rr) (Context env' e)
                             return (n,e')
                        | (n,e) <- bds
                        ]
                   return $ Rec bds'


instance Term (Expr Id) where
  type Generic (Expr Id) = Blob

  select (ExprBlob expr) = return expr
  select _              = Nothing
  inject                = ExprBlob


  allR rr = rewrite $ \ (Context c e) -> case e of
          Var {} -> return e
          Lit {} -> return e
          App e1 e2 ->
                do e1' <- apply (extractR rr) (Context c e1)
                   e2' <- apply (extractR rr) (Context c e2)
                   return $ App e1' e2'
          Lam b e ->
                do e' <- apply (extractR rr) (Context (addHermitEnvLambdaBinding b c) e)
                   return $ Lam b e'
          Let bds e ->
                do
                   -- use *original* env, because the bindings are self-binding,
                   -- if they are recursive. See allR (Rec ...) for details.
                   bds' <- apply (extractR rr) (Context c bds)
                   let c' = addHermitBinding bds c
                   e'   <- apply (extractR rr) (Context c' e)
                   return $ Let bds' e'
          Cast e cast ->
                do e' <- apply (extractR rr) (Context c e)
                   return $ Cast e' cast
          Tick tk e ->
                do e' <- apply (extractR rr) (Context c e)
                   return $ Tick tk e'
                -- Not sure about this. Should be descend into the type here?
                -- If we do so, we should also descend into the types
                -- inside Coercion, Id, etc.
          Type _ty -> return $ e
          Coercion _c -> return $ e

  crushU t = translate $ \ (Context c e) -> case e of
          Var {} -> return mempty
          Lit {} -> return mempty
          App e1 e2 ->
                do r1' <- apply (extractU t) (Context c e1)
                   r2' <- apply (extractU t) (Context c e2)
                   return $ r1' `mappend` r2'
          Lam b e ->
                do e' <- apply (extractU t) (Context (addHermitEnvLambdaBinding b c) e)
                   return $ e'

          _ -> error "TODO: complete please"

{-
-- Need to define thse
appR :: Rewrite (Expr Id) -> Rewrite (Expr Id) -> Rewrite (Expr Id)
appR r1 r2 = rewrite $ \ c e -> case e of
          App e1 e2 ->
                do e1' <- apply r1 c e1
                   e2' <- apply r2 c e2
                   return $ App e1' e2'
          _ -> fail "appR: not App"
-}

--------------------------------------------------------

yieldR :: (Term a, Generic a ~ Blob) => Rewrite a
yieldR = rewrite $ \ cxt@(Context _ a) -> do
                yieldM (fmap inject cxt)
                return a

rewriteTransformerToTranslate
        :: (Term b, Generic b ~ Blob)
        => (Rewrite b -> Rewrite a)
        -> Translate a [Context (Generic b)]
rewriteTransformerToTranslate rrT = translate $ \ (Context c a) -> do
        collectYieldM (apply (rrT yieldR) (Context c a))

collectYieldM :: HermitM a -> HermitM [Context Blob]
collectYieldM (HermitM m) = HermitM $ do
        r <- m
        case r of
          SuccessR _     -> return $ SuccessR []
          FailR   msg    -> return $ FailR msg
          YieldR _ cxts  -> return $ SuccessR cxts
