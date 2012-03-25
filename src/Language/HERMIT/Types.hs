{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

module Language.HERMIT.Types where

import GhcPlugins
import qualified Data.Map as Map
import Data.Monoid

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad

----------------------------------------------------------------------------

-- | Our unit of operation and key type, a 'Translate'.
newtype Translate exp1 exp2 = Translate (HermitEnv -> exp1 -> HermitM exp2)

-- | 'apply' directly applies a 'Translate' value to an argument.
apply :: Translate exp1 exp2 -> HermitEnv -> exp1 -> HermitM exp2
apply (Translate t) env exp1 = t env exp1

-- | 'translate' is the standard way of building a 'Translate'.
translate :: (HermitEnv -> exp1 -> HermitM exp2) -> Translate exp1 exp2
translate = Translate

-- Type synonym for endomorphic translation.
type Rewrite exp = Translate exp exp

-- | 'rewrite' is our primitive way of building a Rewrite,
--
-- @rewrite $ \\ _ e -> return e@ /is/ (now) an identity rewrite.
rewrite :: (HermitEnv -> exp -> HermitM exp) -> Rewrite exp
rewrite = translate

---------------------------------------------------------------------

-- | 'extractR' converts a 'Rewrite' over a 'Generic' into a rewrite over a specific expression type.
extractR  :: (Term exp) => Rewrite  (Generic exp) -> Rewrite  exp	-- at *this* type
extractR rr = rewrite $ \ c e -> do
            e' <- apply rr c (inject e)
            case select e' of
                Nothing -> fail "extractR"
                Just r -> return r

-- | 'extractU' converts a 'Translate' taking a 'Generic' into a translate over a specific expression type.
extractU  :: (Term exp) => Translate  (Generic exp) r -> Translate  exp r
extractU rr = translate $ \ c e -> apply rr c (inject e)

-- | 'promoteR' promotes a 'Rewrite' into a 'Generic' 'Rewrite'; other types inside Generic cause failure.
-- 'try' can be used to convert a failure-by-default promotion into a 'id-by-default' promotion.
promoteR  :: (Term exp) => Rewrite  exp -> Rewrite  (Generic exp)
promoteR rr = rewrite $ \ c e -> do
               case select e of
                 Nothing -> fail "promoteR"
                 Just e' -> do
                    r <- apply rr c e'
                    return (inject r)

-- | 'promoteU' promotes a 'Translate' into a 'Generic' 'Translate'; other types inside Generic cause failure.
promoteU  :: (Term exp) => Translate  exp r -> Translate  (Generic exp) r
promoteU rr = translate $ \ c e -> do
               case select e of
                 Nothing -> fail "promoteI"
                 Just e' -> apply rr c e'

----------------------------------------------------------------------------


-- To rename
data Blob
        = ModGutsBlob   ModGuts
        | BindBlob      (Bind Id)
        | ExprBlob      (Expr Id)
        | TypeBlob      Type

class Term exp where
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

  select (BindBlob expr) = return expr
  select _              = Nothing
  inject                = BindBlob

  allR rr = rewrite $ \ c e -> case e of
          NonRec n e1 -> do
                   e1' <- apply (extractR rr) c e1
                   return $ NonRec n e1'
          Rec bds -> do
                  -- Notice how we add the scoping bindings
                  -- here *before* decending into the rhss.
                   let c' = addHermitBinding (Rec bds) c
                   bds' <- sequence
                        [ do e' <- apply (extractR rr) c' e
                             return (n,e')
                        | (n,e) <- bds
                        ]
                   return $ Rec bds'

instance Term (Expr Id) where
  type Generic (Expr Id) = Blob

  select (ExprBlob expr) = return expr
  select _              = Nothing
  inject                = ExprBlob

  allR rr = rewrite $ \ c e -> case e of
          Var {} -> return e
          Lit {} -> return e
          App e1 e2 ->
                do e1' <- apply (extractR rr) c e1
                   e2' <- apply (extractR rr) c e2
                   return $ App e1' e2'
          Lam b e ->
                do e' <- apply (extractR rr) (addHermitEnvLambdaBinding b c) e
                   return $ Lam b e'
          Let bds e ->
                do
                   -- use *original* env, because the bindings are self-binding,
                   -- if they are recursive. See allR (Rec ...) for details.
                   bds' <- apply (extractR rr) c bds
                   let c' = addHermitBinding bds c
                   e'   <- apply (extractR rr) c' e
                   return $ Let bds' e'

          Cast e cast ->
                do e' <- apply (extractR rr) c e
                   return $ Cast e' cast
          Tick tk e ->
                do e' <- apply (extractR rr) c e
                   return $ Tick tk e'
                -- Not sure about this. Should be descend into the type here?
                -- If we do so, we should also descend into the types
                -- inside Coercion, Id, etc.
          Type _ty -> return $ e
          Coercion _c -> return $ e

  crushU t = translate $ \ c e -> case e of
          Var {} -> return mempty
          Lit {} -> return mempty
          App e1 e2 ->
                do r1' <- apply (extractU t) c e1
                   r2' <- apply (extractU t) c e2
                   return $ r1' `mappend` r2'
          Lam b e ->
                do e' <- apply (extractU t) (addHermitEnvLambdaBinding b c) e
                   return $ e'
