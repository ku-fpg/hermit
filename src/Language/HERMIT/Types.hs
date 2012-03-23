{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

module Language.HERMIT.Types where

import GhcPlugins
import qualified Data.Map as Map

----------------------------------------------------------------------------
-- The transformation/HERMIT monad
newtype HermitM a = HermitM a    -- id, for now

instance Monad HermitM where
        return a = HermitM a

----------------------------------------------------------------------------

-- The bindings here are lazy by choice, so that we can avoid the cost
-- of building the environment, if we never use it.
data HermitEnv = HermitEnv
        { hermitBindings :: Map.Map Id HermitBinding    -- ^ all (important) bindings in scope
        , hermitDepth    :: Int                         -- ^ depth of bindings
        }

data HermitBinding
        = LAM  Int -- all you know is that lambda bound this



hermitBindingDepth :: HermitBinding -> Int
hermitBindingDepth (LAM d) = d

-- A binding you know nothing about, except it may shadow something.
-- If so, do not worry about it here, just remember the binding a the depth.
-- When we want to inline a value from the environment,
-- we *then* check to see what is free in the inlinee, and see
-- if any of the frees will stop the validity of the inlining.

addHermitEnvLambdaBinding :: Id -> HermitEnv -> HermitEnv
addHermitEnvLambdaBinding n env
        = env { hermitBindings = Map.insert n (LAM next_depth) (hermitBindings env)
              , hermitDepth    = next_depth
              }
  where
        next_depth = succ (hermitDepth env)


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
                do let c' = c
                   bds' <- apply (extractR rr)
                                 (case bds of
                                    NonRec {} -> c   -- use original env
                                    Rec {}    -> c') -- use augmented env
                                 bds
                   e'   <- apply (extractR rr) c' e
                   return $ Let bds' e'


{-
          Let bds e ->
          Case e b t alts ->
                do
          Cast e c  ->
          Tick tk e ->
          Type t    ->
          Coercion c ->
  | Lam   b (Expr b)
  | Let   (Bind b) (Expr b)
  | Case  (Expr b) b Type [Alt b]       -- See #case_invariant#
  | Cast  (Expr b) Coercion
  | Tick  (Tickish Id) (Expr b)
  | Type  Type
  | Coercion Coercion
-}