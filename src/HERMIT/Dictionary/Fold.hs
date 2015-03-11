{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
module HERMIT.Dictionary.Fold
    ( -- * Fold/Unfold Transformation
      externals
    , foldR
    , foldVarR
    , foldVarConfigR
    , runFoldR
      -- * Unlifted fold interface
    , fold, compileFold, runFold, runFoldMatches, CompiledFold
      -- * Equality
    , Equality(..)
    , toEqualities
    , flipEquality
    , freeVarsEquality
    , ppEqualityT
    ) where

import Control.Arrow
import Control.Monad
import Control.Monad.IO.Class

import Data.List (delete, (\\), intersect)
import qualified Data.Map as M
import Data.Maybe (catMaybes, fromMaybe, maybeToList)
import qualified Data.IntMap.Lazy as I
import Data.Typeable

import HERMIT.Core
import HERMIT.Context
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Monad
import HERMIT.Name
import HERMIT.Utilities

import HERMIT.Dictionary.Common (varBindingDepthT,findIdT)
import HERMIT.Dictionary.Inline hiding (externals)

import HERMIT.PrettyPrinter.Common
import qualified Text.PrettyPrint.MarkedHughesPJ as PP

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: [External]
externals =
    [ external "fold" (promoteExprR . foldR :: HermitName -> RewriteH Core)
        [ "fold a definition"
        , ""
        , "double :: Int -> Int"
        , "double x = x + x"
        , ""
        , "5 + 5 + 6"
        , "any-bu (fold 'double)"
        , "double 5 + 6"
        , ""
        , "Note: due to associativity, if you wanted to fold 5 + 6 + 6, "
        , "you first need to apply an associativity rewrite." ]  .+ Context .+ Deep
    ]

------------------------------------------------------------------------

foldR :: (ReadBindings c, HasHermitMEnv m, HasHscEnv m, MonadCatch m, MonadIO m, MonadThings m, MonadUnique m)
      => HermitName -> Rewrite c m CoreExpr
foldR nm = prefixFailMsg "Fold failed: " $ findIdT nm >>= foldVarR Nothing

foldVarR :: (ReadBindings c, MonadCatch m, MonadUnique m) => Maybe BindingDepth -> Var -> Rewrite c m CoreExpr
foldVarR = foldVarConfigR AllBinders

foldVarConfigR :: (ReadBindings c, MonadCatch m, MonadUnique m)
               => InlineConfig -> Maybe BindingDepth -> Var -> Rewrite c m CoreExpr
foldVarConfigR config md v = do
    case md of
        Nothing    -> return ()
        Just depth -> do depth' <- varBindingDepthT v
                         guardMsg (depth == depth') "Specified binding depth does not match that of variable binding, this is probably a shadowing occurrence."
    rhss <- liftM (map fst) $ getUnfoldingsT config <<< return v
    transform $ \ c -> maybeM "no match." . fold [mkEquality [] rhs (varToCoreExpr v) | rhs <- rhss] c

-- | Rewrite using a compiled fold. Useful inside traversal strategies like
-- anytdR, because you can compile the fold once outside the traversal, then
-- apply it everywhere in the tree.
runFoldR :: (BoundVars c, Monad m) => CompiledFold -> Rewrite c m CoreExpr
runFoldR compiled = transform $ \c -> maybeM "no match." . runFold compiled c

------------------------------------------------------------------------

newtype CompiledFold = CompiledFold (EMap ([Var], CoreExpr))

-- | Attempt to apply a list of Equalitys to the given expression, folding the
-- left-hand side into an application of the right-hand side. This
-- implementation depends on `Equality` being well-formed. That is, both the
-- LHS and RHS are NOT lambda expressions. Always use `mkEquality` to ensure
-- this is the case.
fold :: BoundVars c => [Equality] -> c -> CoreExpr -> Maybe CoreExpr
fold = runFold . compileFold

-- | Compile a list of Equality's into a single fold matcher.
compileFold :: [Equality] -> CompiledFold
compileFold = CompiledFold . foldr addFold fEmpty
    where addFold (Equality vs lhs rhs) =
            let hs = vs `intersect` varSetElems (freeVarsExpr lhs)
            in insertFold emptyAlphaEnv vs lhs (hs, rhs)

-- | Attempt to fold an expression using a matcher in a given context.
runFold :: BoundVars c => CompiledFold -> c -> CoreExpr -> Maybe CoreExpr
runFold f c e = fst <$> runFoldMatches f c e

-- | Attempt to fold an expression using a matcher in a given context.
-- Return resulting expression and a map of what when in the holes in the pattern.
runFoldMatches :: BoundVars c => CompiledFold -> c -> CoreExpr -> Maybe (CoreExpr, VarEnv CoreExpr)
runFoldMatches (CompiledFold f) c exp = do
    (hs, (vs', rhs')) <- soleElement $ filterOutOfScope c $ findFold exp f
    args <- sequence [ lookupVarEnv hs v | v <- vs' ]
    return (uncurry mkCoreApps $ betaReduceAll (mkCoreLams vs' rhs') args, hs)

insertFold :: Fold m => AlphaEnv -> [Var] -> Key m -> a -> m a -> m a
insertFold env vs k x = fAlter env vs k (const (Just x))

findFold :: Fold m => Key m -> m a -> [(VarEnv CoreExpr, a)]
findFold = fFold emptyVarEnv emptyAlphaEnv

filterOutOfScope :: BoundVars c => c -> [(VarEnv CoreExpr, ([Var], CoreExpr))] -> [(VarEnv CoreExpr, ([Var], CoreExpr))]
filterOutOfScope c = go
    where go [] = []
          go (x@(_,(vs,e)):r)
            | isEmptyVarSet (filterVarSet (not . inScope c) (delVarSetList (freeVarsExpr e) vs)) = x : go r
            | otherwise = go r

------------------------------------------------------------------------

data AlphaEnv = AE { _aeNext :: Int, _aeEnv :: VarEnv Int }

emptyAlphaEnv :: AlphaEnv
emptyAlphaEnv = AE 0 emptyVarEnv

extendAlphaEnv :: Var -> AlphaEnv -> AlphaEnv
extendAlphaEnv v (AE i env) = AE (i+1) (extendVarEnv env v i)

lookupAlphaEnv :: Var -> AlphaEnv -> Maybe Int
lookupAlphaEnv v (AE _ env) = lookupVarEnv env v

------------------------------------------------------------------------

-- TODO: Maybe a -> a ??? -- we never need to delete
type A a = Maybe a -> Maybe a

toA :: Fold m => (m a -> m a) -> Maybe (m a) -> Maybe (m a)
toA f = Just . f . fromMaybe fEmpty

type LMap a = M.Map Literal a
type BMap = TyMap -- Binders are de-bruijn indexed, so we only compare their types

------------------------------------------------------------------------

class Fold m where
    type Key m :: *
    fEmpty :: m a
    fAlter :: AlphaEnv -> [Var] -> Key m -> A a -> m a -> m a
    fFold :: VarEnv CoreExpr -> AlphaEnv -> Key m -> m a -> [(VarEnv CoreExpr, a)]

-- TODO: Idea ... Generalized Tries with Effects
--       Reader - De Bruijn indexing
--       State-ish - Folding with hole filling

------------------------------------------------------------------------

-- Note [Var Uniques]
-- Free variable occurrences can have the same unique at a different type!
-- The reason is that when GHC substitutes into the type of the Var, it DOES NOT
-- freshen the unique of the Var. This is not normally a problem for GHC, because
-- if two Vars with the same unique are bound within scope of each other, one gets
-- freshened at creation. However, with Lemmas, we have the possibility of applying
-- a fold from one subtree to a completely different subtree, so can cross scopes.
--
-- To solve this, we first look up the Var by unique, then check it's type with a TyMap.
-- This is unnecessary for bound vars, because their types are checked when we pass
-- the binding itself.

data VMap a = VM { bvmap :: I.IntMap a, fvmap :: VarEnv (TyMap a) } -- See Note [Var Uniques]
            | VMEmpty

instance Fold VMap where
    type Key VMap = Var

    fEmpty :: VMap a
    fEmpty = VMEmpty

    fAlter :: AlphaEnv -> [Var] -> Key VMap -> A a -> VMap a -> VMap a
    fAlter env vs v f VMEmpty = fAlter env vs v f (VM I.empty emptyVarEnv)
    fAlter env vs v f m@VM{}
        | Just bv <- lookupAlphaEnv v env = m { bvmap = I.alter f bv (bvmap m) }
        | otherwise                       = m { fvmap = alterVarEnv (toA (fAlter env vs (varType v) f)) (fvmap m) v }

    fFold :: VarEnv CoreExpr -> AlphaEnv -> Key VMap -> VMap a -> [(VarEnv CoreExpr, a)]
    fFold _  _   _ VMEmpty = []
    fFold hs env v m@VM{}
        | Just bv <- lookupAlphaEnv v env = maybeToList $ (hs,) <$> I.lookup bv (bvmap m)
        | otherwise                       = do
            m' <- maybeToList $ lookupVarEnv (fvmap m) v
            fFold hs env (varType v) m'

------------------------------------------------------------------------

data TyMap a = TyMEmpty
             | TyM { tmHole   :: TyMap (M.Map Var a)
                   , tmVar    :: VMap a
                   , tmApp    :: TyMap (TyMap a)
                   , tmFun    :: TyMap (TyMap a)
                   , tmTcApp  :: NameEnv (ListMap TyMap a)
                   , tmForall :: TyMap (BMap a)
                   , tmTyLit  :: TyLitMap a
                   }

instance Fold TyMap where
    type Key TyMap = Type

    fEmpty :: TyMap a
    fEmpty = TyMEmpty

    fAlter :: AlphaEnv -> [Var] -> Key TyMap -> A a -> TyMap a -> TyMap a
    fAlter env vs ty f TyMEmpty = fAlter env vs ty f (TyM fEmpty fEmpty fEmpty fEmpty emptyNameEnv fEmpty fEmpty)
    fAlter env vs ty f m@TyM{} = go ty
        where go (TyVarTy v)
                | v `elem` vs  = m { tmHole = fAlter env vs (varType v) (Just . M.alter f v . fromMaybe M.empty) (tmHole m) }
                | otherwise    = m { tmVar = fAlter env vs v f (tmVar m) }
              go (AppTy t1 t2) = m { tmApp = fAlter env vs t1 (toA (fAlter env vs t2 f)) (tmApp m) }
              go (FunTy t1 t2) = m { tmFun = fAlter env vs t1 (toA (fAlter env vs t2 f)) (tmFun m) }
              go (TyConApp tc tys) = m { tmTcApp = alterNameEnv (toA (fAlter env vs tys f)) (tmTcApp m) (getName tc) }
              go (ForAllTy tv t) = m { tmForall = fAlter (extendAlphaEnv tv env) (delete tv vs) t
                                                         (toA (fAlter env vs (varType tv) f)) (tmForall m) }
              go (LitTy l)     = m { tmTyLit = fAlter env vs l f (tmTyLit m) }

    fFold :: VarEnv CoreExpr -> AlphaEnv -> Key TyMap -> TyMap a -> [(VarEnv CoreExpr, a)]
    fFold _ _ _ TyMEmpty = []
    fFold hs env ty m@TyM{} = hss ++ go ty
        where hss = do
                (hs', m') <- fFold hs env (typeKind ty) (tmHole m)
                extendResult m' (Type ty) hs'

              go (TyVarTy v) = fFold hs env v (tmVar m)
              go (AppTy t1 t2) = do
                (hs', m') <- fFold hs env t1 (tmApp m)
                fFold hs' env t2 m'
              go (FunTy t1 t2) = do
                (hs', m') <- fFold hs env t1 (tmFun m)
                fFold hs' env t2 m'
              go (TyConApp tc tys) = maybeToList (lookupNameEnv (tmTcApp m) (getName tc)) >>= fFold hs env tys
              go (ForAllTy tv t) = do
                (hs', m') <- fFold hs (extendAlphaEnv tv env) t (tmForall m)
                fFold hs' env (varType tv) m'
              go (LitTy l) = fFold hs env l (tmTyLit m)

------------------------------------------------------------------------

data TyLitMap a = TLM { tlmNumber :: M.Map Integer a
                      , tlmString :: M.Map FastString a
                      }

instance Fold TyLitMap where
    type Key TyLitMap = TyLit

    fEmpty :: TyLitMap a
    fEmpty = TLM M.empty M.empty

    fAlter :: AlphaEnv -> [Var] -> Key TyLitMap -> A a -> TyLitMap a -> TyLitMap a
    fAlter _ _ l f m = go l
        where go (NumTyLit n) = m { tlmNumber = M.alter f n (tlmNumber m) }
              go (StrTyLit s) = m { tlmString = M.alter f s (tlmString m) }

    fFold :: VarEnv CoreExpr -> AlphaEnv -> Key TyLitMap -> TyLitMap a -> [(VarEnv CoreExpr, a)]
    fFold hs _ l m = go l
        where go (NumTyLit n) = maybeToList $ (hs,) <$> M.lookup n (tlmNumber m)
              go (StrTyLit s) = maybeToList $ (hs,) <$> M.lookup s (tlmString m)

------------------------------------------------------------------------

-- Note [Coercions]
-- We don't actually care about the structure of the coercion evidence
-- itself when we are folding types and expressions. We merely care that
-- there are two coercions with the same type. Hence, we look up the type
-- of the coercion in a TyMap.

-- Note [Tick]
-- We completely look through Ticks, discarding them from pattern expressions
-- at insertion and from candidate expressions at folding/lookup. It is assumed
-- that the Tick is properly present in the RHS, which is the ultimate return
-- value of fFold, thus it will appear in the resulting code.

-- Note [Holes]
-- Holes are distinguished variables which can match any expression. (The universally
-- quantified variables in an Equality.) They are stored as a TyMap, so the type
-- of the expression can be checked against the type of the hole. This wraps a
-- map from Var to result. We use a regular map instead of a VarEnv so we can get
-- the Var back, which allows us to assign it to the expression when building
-- the fold result.

data EMap a = EMEmpty
            | EM { emHole  :: TyMap (M.Map Var a) -- See Note [Holes]
                 , emVar   :: VMap a
                 , emLit   :: LMap a
                 , emCo    :: TyMap a        -- See Note [Coercions]
                 , emType  :: TyMap a
                 , emCast  :: EMap (TyMap a) -- See Note [Coercions]
                 , emApp   :: EMap (EMap a)
                 , emLam   :: EMap (BMap a)
                 , emLetN  :: EMap (EMap (BMap a))
                   -- consider using set rather than list for order-independence
                 , emLetR  :: ListMap EMap (EMap (ListMap BMap a))
                 , emCase  :: EMap (ListMap AMap a)
                 , emECase :: EMap (TyMap a)
                 }

emptyEMapWrapper :: EMap a
emptyEMapWrapper = EM fEmpty fEmpty M.empty fEmpty fEmpty fEmpty
                      fEmpty fEmpty fEmpty fEmpty fEmpty fEmpty

instance Fold EMap where
    type Key EMap = CoreExpr
    fEmpty = EMEmpty

    fAlter :: AlphaEnv -> [Var] -> Key EMap -> A a -> EMap a -> EMap a
    fAlter env vs exp f EMEmpty = fAlter env vs exp f emptyEMapWrapper
    fAlter env vs exp f m@EM{} = go exp
        where go (Var v)
                | v `elem` vs = m { emHole = fAlter env vs (varType v) (Just . M.alter f v . fromMaybe M.empty) (emHole m) }
                | otherwise   = m { emVar  = fAlter env vs v f (emVar m) }
              go (Lit l)      = m { emLit  = M.alter f l (emLit m) }
              go (Coercion c) = m { emCo   = fAlter env vs (coercionType c) f (emCo m) }
              go (Type t)     = m { emType = fAlter env vs t f (emType m) }
              go (Cast e c)   = m { emCast = fAlter env vs e (toA (fAlter env vs (coercionType c) f)) (emCast m) }
              go (Tick _ e)   = fAlter env vs e f m -- See Note [Tick]
              go (App l r)    = m { emApp  = fAlter env vs l (toA (fAlter env vs r f)) (emApp m) }
              go (Lam b e)    = m { emLam  = fAlter (extendAlphaEnv b env) (delete b vs) e
                                                    (toA (fAlter env vs (varType b) f))
                                                    (emLam m) }
              go (Case s _ t []) = m { emECase = fAlter env vs s (toA (fAlter env vs t f)) (emECase m) }
              go (Case s b _ as) = m { emCase = fAlter env vs s
                                                       (toA (fAlter (extendAlphaEnv b env) (delete b vs) as f))
                                                       (emCase m) }
              go (Let (NonRec b r) e) = m { emLetN = fAlter (extendAlphaEnv b env) (delete b vs) e
                                                            (toA (fAlter env vs r (toA (fAlter env vs (varType b) f))))
                                                            (emLetN m) }
              go (Let (Rec ds) e) = let (bs, rhss) = unzip ds
                                        env' = foldr extendAlphaEnv env bs
                                        vs' = vs \\ bs
                                    in m { emLetR = fAlter env' vs' rhss
                                                           (toA (fAlter env' vs' e
                                                                        (toA (fAlter env vs (map varType bs) f))))
                                                           (emLetR m) }

    fFold :: VarEnv CoreExpr -> AlphaEnv -> Key EMap -> EMap a -> [(VarEnv CoreExpr, a)]
    fFold _  _   _ EMEmpty = []
    fFold hs env exp m@EM{} = hss ++ go exp
        where hss = do
                (hs', m') <- fFold hs env (exprKindOrType exp) (emHole m)
                extendResult m' exp hs'

              go (Var v)      = fFold hs env v (emVar m)
              go (Lit l)      = maybeToList $ (hs,) <$> M.lookup l (emLit m)
              go (Coercion c) = fFold hs env (coercionType c) (emCo m)
              go (Type t)     = fFold hs env t (emType m)
              go (Cast e c)   = do
                (hs', m') <- fFold hs env e (emCast m)
                fFold hs' env (coercionType c) m'
              go (Tick _ e)   = fFold hs env e m -- See Note [Tick]
              go (App l r)    = do
                (hs', m') <- fFold hs env l (emApp m)
                fFold hs' env r m'
              go (Lam b e)    = do
                (hs', m') <- fFold hs (extendAlphaEnv b env) e (emLam m)
                fFold hs' env (varType b) m'
              go (Case s _ t []) = do
                (hs', m') <- fFold hs env s (emECase m)
                fFold hs' env t m'
              go (Case s b _ as) = do
                (hs', m') <- fFold hs env s (emCase m)
                fFold hs' (extendAlphaEnv b env) as m'
              go (Let (NonRec b r) e) = do
                (hs' , m' ) <- fFold hs (extendAlphaEnv b env) e (emLetN m)
                (hs'', m'') <- fFold hs' env r m'
                fFold hs'' env (varType b) m''
              go (Let (Rec ds) e) = do
                let (bs, rhss) = unzip ds
                    env' = foldr extendAlphaEnv env bs
                (hs' , m' ) <- fFold hs env' rhss (emLetR m)
                (hs'', m'') <- fFold hs' env' e m'
                fFold hs'' env (map varType bs) m''

-- Add the matched expression to the holes map, fails if expression differs from one already in hole.
extendResult :: M.Map Var a -> CoreExpr -> VarEnv CoreExpr -> [(VarEnv CoreExpr, a)]
extendResult hm e m = catMaybes
    [ case lookupVarEnv m v of
        Nothing -> return (extendVarEnv m v e, x)
        Just e' -> sameExpr e e' >> return (m, x)
    | (v,x) <- M.assocs hm ]

-- | Determine if two expressions are alpha-equivalent.
sameExpr :: CoreExpr -> CoreExpr -> Maybe ()
sameExpr e1 e2 = snd <$> soleElement (findFold e2 m)
    where m = insertFold emptyAlphaEnv [] e1 () EMEmpty

------------------------------------------------------------------------

data ListMap m a
  = ListMap { lmNil  :: Maybe a
            , lmCons :: m (ListMap m a) }

instance Fold m => Fold (ListMap m) where
    type Key (ListMap m) = [Key m]

    fEmpty :: ListMap m a
    fEmpty = ListMap Nothing fEmpty

    fAlter :: AlphaEnv -> [Var] -> Key (ListMap m) -> A a -> ListMap m a -> ListMap m a
    fAlter _   _  []     f m = m { lmNil  = f (lmNil m) }
    fAlter env vs (x:xs) f m = m { lmCons = fAlter env vs x (toA (fAlter env vs xs f)) (lmCons m) }

    fFold :: VarEnv CoreExpr -> AlphaEnv -> Key (ListMap m) -> ListMap m a -> [(VarEnv CoreExpr, a)]
    fFold hs _   []     m = maybeToList $ (hs,) <$> lmNil m
    fFold hs env (x:xs) m = do
        (hs', m') <- fFold hs env x (lmCons m)
        fFold hs' env xs m'

------------------------------------------------------------------------

-- Note [Alt Binders]
-- We don't store the uniques/types of the alt-binders, because they are
-- completely determined by the scrutinee/datacon/rhs.

data AMap a = AMEmpty
            | AM { amDef  :: EMap a
                 , amData :: NameEnv (EMap a) -- See Note [Alt Binders]
                 , amLit  :: LMap (EMap a) }

instance Fold AMap where
    type Key AMap = Alt CoreBndr

    fEmpty :: AMap a
    fEmpty = AMEmpty

    fAlter :: AlphaEnv -> [Var] -> Key AMap -> A a -> AMap a -> AMap a
    fAlter env vs alt f AMEmpty = fAlter env vs alt f (AM fEmpty emptyNameEnv M.empty)
    fAlter env vs alt f m@AM{} = go alt
        where go (DEFAULT  , _ , rhs) = m { amDef  = fAlter env vs rhs f (amDef m) }
              go (DataAlt d, bs, rhs) = m { amData = alterNameEnv
                                                        (toA (fAlter (foldr extendAlphaEnv env bs) (vs \\ bs) rhs f))
                                                        (amData m) (getName d) }
              go (LitAlt l , _ , rhs) = m { amLit  = M.alter (toA (fAlter env vs rhs f)) l (amLit m) }

    fFold :: VarEnv CoreExpr -> AlphaEnv -> Key AMap -> AMap a -> [(VarEnv CoreExpr, a)]
    fFold _ _ _ AMEmpty = []
    fFold hs env alt m@AM{} = go alt
        where go (DEFAULT  , _ , rhs) = fFold hs env rhs (amDef m)
              go (DataAlt d, bs, rhs) = do
                m' <- maybeToList (lookupNameEnv (amData m) (getName d))
                fFold hs (foldr extendAlphaEnv env bs) rhs m'
              go (LitAlt l , _ , rhs) = maybeToList (M.lookup l (amLit m)) >>= fFold hs env rhs

----------------------------------------------------------------------------

-- | An equality is represented as a set of universally quantified binders, and the LHS and RHS of the equality.
data Equality = Equality [CoreBndr] CoreExpr CoreExpr

-- | Build an equality from a list of universally quantified binders and two expressions.
-- If the head of either expression is a lambda expression, it's binder will become a universally quantified binder
-- over both sides. It is assumed the two expressions have the same type.
--
-- Ex.    mkEquality [] (\x. foo x) bar === forall x. foo x = bar x
--        mkEquality [] (baz y z) (\x. foo x x) === forall x. baz y z x = foo x x
--        mkEquality [] (\x. foo x) (\y. bar y) === forall x. foo x = bar x
mkEquality :: [CoreBndr] -> CoreExpr -> CoreExpr -> Equality
mkEquality vs lhs rhs = case mkQuantified vs lhs rhs of
                            Quantified vs' (Equiv lhs' rhs') -> Equality vs' lhs' rhs'

toEqualities :: Quantified -> [Equality]
toEqualities = go []
    where go qs (Quantified vs cl) = go2 (qs++vs) cl

          go2 qs (Equiv e1 e2) = [mkEquality qs e1 e2]
          go2 qs (Conj q1 q2)  = go qs q1 ++ go qs q2
          go2 _  _             = []

ppEqualityT :: PrettyPrinter -> PrettyH Equality
ppEqualityT pp = do
    Equality bs lhs rhs <- idR
    dfa <- return bs >>> pForall pp
    d1 <- return lhs >>> extractT (pCoreTC pp)
    d2 <- return rhs >>> extractT (pCoreTC pp)
    return $ PP.sep [dfa,d1,PP.text "=",d2]

------------------------------------------------------------------------------

-- | Flip the LHS and RHS of a 'Equality'.
flipEquality :: Equality -> Equality
flipEquality (Equality xs lhs rhs) = Equality xs rhs lhs

------------------------------------------------------------------------------

{-
-- Idea: use Haskell's functions to fill the holes automagically
--
-- plusId <- findIdT "+"
-- timesId <- findIdT "*"
-- mkEquality $ \ x -> ( mkCoreApps (Var plusId)  [x,x]
--                     , mkCoreApps (Var timesId) [Lit 2, x])
--
-- TODO: need to know type of 'x' to generate a variable.
class BuildEquality a where
    mkEquality :: a -> HermitM Equality

instance BuildEquality (CoreExpr,CoreExpr) where
    mkEquality :: (CoreExpr,CoreExpr) -> HermitM Equality
    mkEquality (lhs,rhs) = return $ Equality [] lhs rhs

instance BuildEquality a => BuildEquality (CoreExpr -> a) where
    mkEquality :: (CoreExpr -> a) -> HermitM Equality
    mkEquality f = do
        x <- newIdH "x" (error "need to create a type")
        Equality bnds lhs rhs <- mkEquality (f (varToCoreExpr x))
        return $ Equality (x:bnds) lhs rhs
-}

------------------------------------------------------------------------------

freeVarsEquality :: Equality -> VarSet
freeVarsEquality (Equality bs lhs rhs) =
    delVarSetList (unionVarSets (map freeVarsExpr [lhs,rhs])) bs

------------------------------------------------------------------------------

data RewriteEqualityBox = RewriteEqualityBox (RewriteH Equality) deriving Typeable

instance Extern (RewriteH Equality) where
    type Box (RewriteH Equality) = RewriteEqualityBox
    box = RewriteEqualityBox
    unbox (RewriteEqualityBox r) = r

-----------------------------------------------------------------

data TransformEqualityStringBox = TransformEqualityStringBox (TransformH Equality String) deriving Typeable

instance Extern (TransformH Equality String) where
    type Box (TransformH Equality String) = TransformEqualityStringBox
    box = TransformEqualityStringBox
    unbox (TransformEqualityStringBox t) = t

-----------------------------------------------------------------

data TransformEqualityUnitBox = TransformEqualityUnitBox (TransformH Equality ()) deriving Typeable

instance Extern (TransformH Equality ()) where
    type Box (TransformH Equality ()) = TransformEqualityUnitBox
    box = TransformEqualityUnitBox
    unbox (TransformEqualityUnitBox i) = i

