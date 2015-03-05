{-# LANGUAGE DeriveDataTypeable #-}

module HERMIT.Lemma
    ( -- * Quantified
      Quantified(..)
    , mkQuantified
    , Clause(..)
    , instQuantified
    , instsQuantified
    , discardUniVars
    , freeVarsQuantified
    , substQuantified
    , substQuantifieds
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
import Language.KURE.MonadCatch

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

-- | Assumes Var is free in Quantified. If not, no substitution will happen, though uniques might be freshened.
substQuantified :: Var -> CoreArg -> Quantified -> Quantified
substQuantified v e = substQuantifieds [(v,e)]

substQuantifieds :: [(Var,CoreArg)] -> Quantified -> Quantified
substQuantifieds ps q = substQuantifiedSubst (extendSubstList sub ps) q
    where (vs,es) = unzip ps
          sub = mkEmptySubst
              $ mkInScopeSet
              $ delVarSetList (unionVarSets $ freeVarsQuantified q : map freeVarsExpr es) vs

-- | Note: Subst must be properly set up with an InScopeSet that includes all vars
-- in scope in the *range* of the substitution.
substQuantifiedSubst :: Subst -> Quantified -> Quantified
substQuantifiedSubst = go
    where go sub (Quantified bs cl) =
            let (bs', cl') = go1 sub bs [] cl
            in Quantified bs' cl'

          go1 subst [] bs' cl = (reverse bs', go2 subst cl)
          go1 subst (b:bs) bs' cl =
            let (subst',b') = substBndr subst b
            in go1 subst' bs (b':bs') cl
          go2 subst (Conj q1 q2) = Conj (go subst q1) (go subst q2)
          go2 subst (Disj q1 q2) = Disj (go subst q1) (go subst q2)
          go2 subst (Impl q1 q2) = Impl (go subst q1) (go subst q2)
          go2 subst (Equiv e1 e2) =
            let e1' = substExpr (text "substQuantified e1") subst e1
                e2' = substExpr (text "substQuantified e2") subst e2
            in Equiv e1' e2'

------------------------------------------------------------------------------

-- | Instantiate one of the universally quantified variables in a 'Quantified'.
-- Note: assumes implicit ordering of variables, such that substitution happens to the right
-- as it does in case alternatives. Only first variable that matches predicate is
-- instantiated.
instQuantified :: MonadCatch m => (Var -> Bool) -- predicate to select var
                               -> CoreExpr      -- expression to instantiate with
                               -> Quantified -> m Quantified
instQuantified p e = liftM fst . go []
    where go bbs (Quantified bs cl)
            | not (any p bs) = -- not quantified at this level, so try further down
                let go2 con q1 q2 = do
                        er <- attemptM $ go (bs++bbs) q1
                        (cl',s) <- case er of
                            Right (q1',s) -> return (con q1' q2, s)
                            Left _ -> do
                                er' <- attemptM $ go (bs++bbs) q2
                                case er' of
                                    Right (q2',s) -> return (con q1 q2', s)
                                    Left msg -> fail msg
                        return (replaceVars s bs (Quantified [] cl'), s)
                in case cl of
                    Equiv{} -> fail "specified variable is not universally quantified."
                    Conj q1 q2 -> go2 Conj q1 q2
                    Disj q1 q2 -> go2 Disj q1 q2
                    Impl q1 q2 -> go2 Impl q1 q2

            | otherwise = do -- quantified here, so do substitution and start bubbling up
                let (bs',i:vs) = break p bs -- this is safe because we know i is in bs
                    tyVars = filter isTyVar (bs'++bbs)
                    failMsg = fail "type of provided expression differs from selected binder."

                    bindFn v = if v `elem` tyVars then BindMe else Skolem

                sub <- maybe failMsg return $ tcUnifyTys bindFn [varType i] [exprKindOrType e]

                    -- if i is a tyvar, we know e is a type, so free vars will be tyvars
                let itvs = [ v | isTyVar i, v <- varSetElems (freeVarsExpr e) ]
                    q' = substQuantified i e $ Quantified vs cl

                return (replaceVars sub (bs'++itvs) q', sub)

-- | The function which 'bubbles up' after the instantiation takes place,
-- replacing any type variables that were instantiated as a result of specialization.
replaceVars :: TvSubst -> [Var] -> Quantified -> Quantified
replaceVars sub vs = go (reverse vs)
    where addB b (Quantified bs cl) = Quantified (b:bs) cl

          go [] q = q
          go (b:bs) q
            | isTyVar b = case lookupTyVar sub b of
                            Nothing -> go bs (addB b q)
                            Just ty -> let new = varSetElems (freeVarsType ty)
                                       in go (new++bs) (substQuantified b (Type ty) q)
            | otherwise = go bs (addB b q)

-- tvSubstToSubst :: TvSubst -> Subst
-- tvSubstToSubst (TvSubst inS tEnv) = mkSubst inS tEnv emptyVarEnv emptyVarEnv

-- | Instantiate a set of universally quantified variables in a 'Quantified'.
-- It is important that all type variables appear before any value-level variables in the first argument.
instsQuantified :: MonadCatch m => [(Var,CoreExpr)] -> Quantified -> m Quantified
instsQuantified = flip (foldM (\ q (v,e) -> instQuantified (==v) e q)) . reverse
-- foldM is a left-to-right fold, so the reverse is important to do substitutions in reverse order
-- which is what we want (all value variables should be instantiated before type variables).

------------------------------------------------------------------------------
