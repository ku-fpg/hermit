{-# LANGUAGE DeriveDataTypeable #-}

module HERMIT.Equality
    ( -- * Equality
      Equality(..)
    , mkEquality
    , flipEquality
    , freeVarsEquality
    , instantiateEquality
    , instantiateEqualityVar
    , discardUniVars
      -- * Lemmas
    , LemmaName(..)
    , Lemma(..)
    , Lemmas
    ) where

import Prelude hiding (lookup)

import Control.Monad

import Data.Dynamic (Typeable)
import Data.String (IsString(..))
import qualified Data.Map as M
import Data.Monoid

import HERMIT.Core
import HERMIT.GHC hiding ((<>))

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
mkEquality vs lhs rhs = Equality (tvs++vs++lbs++rbs) lhs' rbody
    where (lbs, lbody) = collectBinders lhs
          rhs' = uncurry mkCoreApps $ betaReduceAll rhs $ map varToCoreExpr lbs
          (rbs, rbody) = collectBinders rhs'
          lhs' = mkCoreApps lbody $ map varToCoreExpr rbs
          -- now quantify over the free type variables
          tvs = varSetElems
              $ filterVarSet isTyVar
              $ freeVarsEquality
              $ Equality (vs++lbs++rbs) lhs' rbody

-- | A name for lemmas. Use a newtype so we can tab-complete in shell.
newtype LemmaName = LemmaName String deriving (Eq, Ord, Typeable)

instance Monoid LemmaName where
    mempty = LemmaName mempty
    mappend (LemmaName n1) (LemmaName n2) = LemmaName (mappend n1 n2)

instance IsString LemmaName where fromString = LemmaName
instance Show LemmaName where show (LemmaName s) = s

-- | An equality with a proven/used status.
data Lemma = Lemma { lemmaEq :: Equality
                   , lemmaP  :: Bool     -- whether lemma has been proven
                   , lemmaU  :: Bool     -- whether lemma has been used
                   }

-- | A collection of named lemmas.
type Lemmas = M.Map LemmaName Lemma

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

discardUniVars :: Equality -> Equality
discardUniVars (Equality _ lhs rhs) = Equality [] lhs rhs

freeVarsEquality :: Equality -> VarSet
freeVarsEquality (Equality bs lhs rhs) =
    delVarSetList (unionVarSets (map freeVarsExpr [lhs,rhs])) bs

------------------------------------------------------------------------------

-- | Instantiate one of the universally quantified variables in a 'Equality'.
-- Note: assumes implicit ordering of variables, such that substitution happens to the right
-- as it does in case alternatives. Only first variable that matches predicate is
-- instantiated.
instantiateEqualityVar :: Monad m => (Var -> Bool) -- predicate to select var
                                  -> CoreExpr      -- expression to instantiate with
                                  -> [Var]         -- new binders to add in place of var
                                  -> Equality -> m Equality
instantiateEqualityVar p e new (Equality bs lhs rhs)
    | not (any p bs) = fail "specified variable is not universally quantified."
    | otherwise = do
        let (bs',i:vs) = break p bs -- this is safe because we know i is in bs
            tyVars    = filter isTyVar bs'
            failMsg   = fail "type of provided expression differs from selected binder."

            bindFn v = if v `elem` tyVars then BindMe else Skolem

        sub <- maybe failMsg (return . tvSubstToSubst) (tcUnifyTys bindFn [varType i] [exprKindOrType e])

        let inS           = delVarSetList (unionVarSets (map localFreeVarsExpr [lhs, rhs, e] ++ map freeVarsVar vs)) (i:vs)
            subst         = extendSubst (addInScopeSet sub inS) i e -- TODO: subst in both of these?
            (subst', vs') = substBndrs subst vs
            lhs'          = substExpr (text "equality-lhs") subst' lhs
            rhs'          = substExpr (text "equality-rhs") subst' rhs
        return $ Equality (bs'++new++vs') lhs' rhs'

tvSubstToSubst :: TvSubst -> Subst
tvSubstToSubst (TvSubst inS tEnv) = mkSubst inS tEnv emptyVarEnv emptyVarEnv

-- | Instantiate a set of universally quantified variables in a 'Equality'.
-- It is important that all type variables appear before any value-level variables in the first argument.
instantiateEquality :: Monad m => [(Var,CoreExpr,[Var])] -> Equality -> m Equality
instantiateEquality = flip (foldM (\ eq (v,e,vs) -> instantiateEqualityVar (==v) e vs eq)) . reverse
-- foldM is a left-to-right fold, so the reverse is important to do substitutions in reverse order
-- which is what we want (all value variables should be instantiated before type variables).

