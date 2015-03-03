{-# LANGUAGE DeriveDataTypeable #-}

module HERMIT.Lemma
    ( -- * Quantified
      Quantified(..)
    , mkQuantified
    , Clause(..)
    , instantiateQuantified
    , instantiateQuantifiedVar
    , discardUniVars
    , freeVarsQuantified
      -- * Lemmas
    , LemmaName(..)
    , Lemma(..)
    , Lemmas
    , NamedLemma
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

-- | Build a Quantified from a list of universally quantified binders and two expressions.
-- If the head of either expression is a lambda expression, it's binder will become a universally quantified binder
-- over both sides. It is assumed the two expressions have the same type.
--
-- Ex.    mkQuantified [] (\x. foo x) bar === forall x. foo x = bar x
--        mkQuantified [] (baz y z) (\x. foo x x) === forall x. baz y z x = foo x x
--        mkQuantified [] (\x. foo x) (\y. bar y) === forall x. foo x = bar x
mkQuantified :: [CoreBndr] -> CoreExpr -> CoreExpr -> Quantified
mkQuantified vs lhs rhs = dropBinders $ Quantified (tvs++vs++lbs++rbs) (Equiv lhs' rbody)
    where (lbs, lbody) = collectBinders lhs
          rhs' = uncurry mkCoreApps $ betaReduceAll rhs $ map varToCoreExpr lbs
          (rbs, rbody) = collectBinders rhs'
          lhs' = mkCoreApps lbody $ map varToCoreExpr rbs
          -- now quantify over the free type variables
          tvs = varSetElems
              $ filterVarSet isTyVar
              $ delVarSetList (unionVarSets $ map freeVarsExpr [lhs',rbody]) (vs++lbs++rbs)

freeVarsQuantified :: Quantified -> VarSet
freeVarsQuantified (Quantified bs cl) = delVarSetList (freeVarsClause cl) bs

freeVarsClause :: Clause -> VarSet
freeVarsClause (Conj  q1 q2) = unionVarSets $ map freeVarsQuantified [q1,q2]
freeVarsClause (Disj  q1 q2) = unionVarSets $ map freeVarsQuantified [q1,q2]
freeVarsClause (Impl  q1 q2) = unionVarSets $ map freeVarsQuantified [q1,q2]
freeVarsClause (Equiv e1 e2) = unionVarSets $ map freeVarsExpr [e1,e2]

dropBinders :: Quantified -> Quantified
dropBinders (Quantified bs cl) =
    case bs of
        []      -> Quantified [] (dropBindersClause cl)
        (b:bs') -> case dropBinders (Quantified bs' cl) of
                    q@(Quantified bs'' cl')
                        | b `elemVarSet` freeVarsQuantified q -> Quantified (b:bs'') cl'
                        | otherwise -> q

dropBindersClause :: Clause -> Clause
dropBindersClause (Conj q1 q2) = Conj (dropBinders q1) (dropBinders q2)
dropBindersClause (Disj q1 q2) = Disj (dropBinders q1) (dropBinders q2)
dropBindersClause (Impl q1 q2) = Impl (dropBinders q1) (dropBinders q2)
dropBindersClause equiv        = equiv


-- | A name for lemmas. Use a newtype so we can tab-complete in shell.
newtype LemmaName = LemmaName String deriving (Eq, Ord, Typeable)

instance Monoid LemmaName where
    mempty = LemmaName mempty
    mappend (LemmaName n1) (LemmaName n2) = LemmaName (mappend n1 n2)

instance IsString LemmaName where fromString = LemmaName
instance Show LemmaName where show (LemmaName s) = s

-- | An equality with a proven/used status.
data Lemma = Lemma { lemmaQ :: Quantified
                   , lemmaP :: Bool     -- whether lemma has been proven
                   , lemmaU :: Bool     -- whether lemma has been used
                   }

data Quantified = Quantified [CoreBndr] Clause

data Clause = Conj Quantified Quantified
            | Disj Quantified Quantified
            | Impl Quantified Quantified
            | Equiv CoreExpr CoreExpr

-- | A collection of named lemmas.
type Lemmas = M.Map LemmaName Lemma

-- | A LemmaName, Lemma pair.
type NamedLemma = (LemmaName, Lemma)

------------------------------------------------------------------------------

discardUniVars :: Quantified -> Quantified
discardUniVars (Quantified _ cl) = Quantified [] cl

------------------------------------------------------------------------------

-- TODO: handle other types of Quantified

-- | Instantiate one of the universally quantified variables in a 'Quantified'.
-- Note: assumes implicit ordering of variables, such that substitution happens to the right
-- as it does in case alternatives. Only first variable that matches predicate is
-- instantiated.
instantiateQuantifiedVar :: Monad m => (Var -> Bool) -- predicate to select var
                                    -> CoreExpr      -- expression to instantiate with
                                    -> [Var]         -- new binders to add in place of var
                                    -> Quantified -> m Quantified
instantiateQuantifiedVar p e new (Quantified bs (Equiv lhs rhs))
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
        return $ Quantified (bs'++new++vs') (Equiv lhs' rhs')

tvSubstToSubst :: TvSubst -> Subst
tvSubstToSubst (TvSubst inS tEnv) = mkSubst inS tEnv emptyVarEnv emptyVarEnv

-- | Instantiate a set of universally quantified variables in a 'Quantified'.
-- It is important that all type variables appear before any value-level variables in the first argument.
instantiateQuantified :: Monad m => [(Var,CoreExpr,[Var])] -> Quantified -> m Quantified
instantiateQuantified = flip (foldM (\ eq (v,e,vs) -> instantiateQuantifiedVar (==v) e vs eq)) . reverse
-- foldM is a left-to-right fold, so the reverse is important to do substitutions in reverse order
-- which is what we want (all value variables should be instantiated before type variables).

------------------------------------------------------------------------------
