{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Lemma
    ( -- * Clause
      Clause(..)
    , mkClause
    , mkForall
    , addBinder
    , collectQs
    , instClause
    , instsClause
    , discardUniVars
    , freeVarsClause
    , clauseSyntaxEq
    , substClause
    , substClauses
    , dropBinders
    , redundantDicts
      -- * Lemmas
    , LemmaName(..)
    , Lemma(..)
    , Proven(..)
    , andP, orP
    , Used(..)
    , Lemmas
    , NamedLemma
    ) where

import Prelude hiding (lookup)

import Control.Monad

import Data.Semigroup (Semigroup(..))
import Data.String (IsString(..))
import qualified Data.Map as M

import GHC.Generics

import HERMIT.Core
import HERMIT.GHC hiding ((<>))
import HERMIT.Exception
import Language.KURE.MonadCatch

import Control.Exception

----------------------------------------------------------------------------

-- | Build a Clause from a list of universally quantified binders and two expressions.
-- If the head of either expression is a lambda expression, it's binder will become a universally quantified binder
-- over both sides. It is assumed the two expressions have the same type.
--
-- Ex.    mkClause [] (\x. foo x) bar === forall x. foo x = bar x
--        mkClause [] (baz y z) (\x. foo x x) === forall x. baz y z x = foo x x
--        mkClause [] (\x. foo x) (\y. bar y) === forall x. foo x = bar x
mkClause :: [CoreBndr] -> CoreExpr -> CoreExpr -> Clause
mkClause vs lhs rhs = redundantDicts $ dropBinders $ mkForall (tvs++vs++lbs++rbs) (Equiv lhs' rbody)
    where (lbs, lbody) = collectBinders lhs
          rhs' = uncurry mkCoreApps $ betaReduceAll rhs $ map varToCoreExpr lbs
          (rbs, rbody) = collectBinders rhs'
          lhs' = mkCoreApps lbody $ map varToCoreExpr rbs
          -- now quantify over the free type variables
          tvs = nonDetEltsUniqSet -- varSetElems
              $ filterVarSet isTyVar
              $ delVarSetList (unionVarSets $ map freeVarsExpr [lhs',rbody]) (vs++lbs++rbs)

freeVarsClause :: Clause -> VarSet
freeVarsClause (Forall b cl)  = delVarSet (freeVarsClause cl) b
freeVarsClause (Conj  q1 q2)  = unionVarSets $ map freeVarsClause [q1,q2]
freeVarsClause (Disj  q1 q2)  = unionVarSets $ map freeVarsClause [q1,q2]
freeVarsClause (Impl _ q1 q2) = unionVarSets $ map freeVarsClause [q1,q2]
freeVarsClause (Equiv e1 e2)  = unionVarSets $ map freeVarsExpr [e1,e2]
freeVarsClause CTrue          = emptyVarSet

dropBinders :: Clause -> Clause
dropBinders (Forall b cl)  =
    let cl' = dropBinders cl
    in if b `elemVarSet` freeVarsClause cl'
       then addBinder b cl'
       else cl'
dropBinders (Conj q1 q2)    = Conj (dropBinders q1) (dropBinders q2)
dropBinders (Disj q1 q2)    = Disj (dropBinders q1) (dropBinders q2)
dropBinders (Impl nm q1 q2) = Impl nm (dropBinders q1) (dropBinders q2)
dropBinders other           = other

addBinder :: CoreBndr -> Clause -> Clause
addBinder = Forall

mkForall :: [CoreBndr] -> Clause -> Clause
mkForall = flip (foldr Forall)

collectQs :: Clause -> ([CoreBndr], Clause)
collectQs (Forall b cl) = (b:bs, cl')
    where (bs, cl') = collectQs cl
collectQs cl            = ([],cl)

-- | A name for lemmas. Use a newtype so we can tab-complete in shell.
newtype LemmaName = LemmaName String deriving (Eq, Ord)

instance Monoid LemmaName where
    mempty = LemmaName mempty
    mappend = (<>)

instance Semigroup LemmaName where
    LemmaName n1 <> LemmaName n2 = LemmaName (n1 <> n2)

instance IsString LemmaName where fromString = LemmaName
instance Show LemmaName where show (LemmaName s) = s

-- | An equality with a proven/used status.
data Lemma = Lemma { lemmaC :: Clause
                   , lemmaP :: Proven     -- whether lemma has been proven
                   , lemmaU :: Used       -- whether lemma has been used
                   }

data Proven = Proven
            | Assumed -- ^ Assumed by user
            | BuiltIn -- ^ Assumed by library/HERMIT
            | NotProven
    deriving Eq

instance Show Proven where
    show Proven = "Proven"
    show Assumed = "Assumed"
    show BuiltIn = "Built In"
    show NotProven = "Not Proven"

instance Enum Proven where
    toEnum 1 = Assumed
    toEnum 2 = BuiltIn
    toEnum 3 = Proven
    toEnum _ = NotProven

    fromEnum NotProven = 0
    fromEnum Assumed = 1
    fromEnum BuiltIn = 2
    fromEnum Proven = 3

-- Ordering: NotProven < Assumed < BuiltIn < Proven
instance Ord Proven where
    compare :: Proven -> Proven -> Ordering
    compare p1 p2 = compare (fromEnum p1) (fromEnum p2)

-- When conjuncting, result is as proven as the least of the two
andP :: Proven -> Proven -> Proven
andP = min

-- When disjuncting, result is as proven as the most of the two
orP :: Proven -> Proven -> Proven
orP = max

data Used = Obligation -- ^ this MUST be proven immediately
          | UnsafeUsed -- ^ used, but can be proven later (only introduced in unsafe shell)
          | NotUsed
    deriving (Eq, Generic)

instance Show Used where
    show Obligation = "Obligation"
    show UnsafeUsed = "Used"
    show NotUsed    = "Not Used"

data Clause = Forall CoreBndr Clause
            | Conj Clause Clause
            | Disj Clause Clause
            | Impl LemmaName Clause Clause -- ^ name for the antecedent when it is in scope
            | Equiv CoreExpr CoreExpr
            | CTrue -- the always true clause

-- | A collection of named lemmas.
type Lemmas = M.Map LemmaName Lemma

-- | A LemmaName, Lemma pair.
type NamedLemma = (LemmaName, Lemma)

------------------------------------------------------------------------------

discardUniVars :: Clause -> Clause
discardUniVars (Forall _ cl) = discardUniVars cl
discardUniVars cl            = cl

------------------------------------------------------------------------------

-- | Assumes Var is free in Clause. If not, no substitution will happen, though uniques might be freshened.
substClause :: Var -> CoreArg -> Clause -> Clause
substClause v e = substClauses [(v,e)]

substClauses :: [(Var,CoreArg)] -> Clause -> Clause
substClauses ps cl = substClauseSubst (extendSubstList sub ps) cl
    where (vs,es) = unzip ps
          sub = mkEmptySubst
              $ mkInScopeSet
              $ delVarSetList (unionVarSets $ freeVarsClause cl : map freeVarsExpr es) vs

-- | Note: Subst must be properly set up with an InScopeSet that includes all vars
-- in scope in the *range* of the substitution.
substClauseSubst :: Subst -> Clause -> Clause
substClauseSubst = go
    where go subst (Forall b cl)   =
            let (subst',b') = substBndr subst b
            in addBinder b' (go subst' cl)
          go _     CTrue           = CTrue
          go subst (Conj q1 q2)    = Conj    (go subst q1) (go subst q2)
          go subst (Disj q1 q2)    = Disj    (go subst q1) (go subst q2)
          go subst (Impl nm q1 q2) = Impl nm (go subst q1) (go subst q2)
          go subst (Equiv e1 e2)   =
            let e1' = substExpr (text "substClauseSubst e1") subst e1
                e2' = substExpr (text "substClauseSubst e2") subst e2
            in Equiv e1' e2'

------------------------------------------------------------------------------

redundantDicts :: Clause -> Clause
redundantDicts = go []
    where go tys (Forall b cl)
            | isDictTy bTy =
                case [ varToCoreExpr pb | (pb,ty) <- tys, eqType bTy ty ] of
                    []     -> addBinder b $ go ((b,bTy):tys) cl -- not seen before
                    (b':_) -> substClause b b' cl               -- seen
            | otherwise = addBinder b (go tys cl)
            where bTy = varType b
          go _ cl = cl

------------------------------------------------------------------------------

-- | Instantiate one of the universally quantified variables in a 'Clause'.
-- Note: assumes implicit ordering of variables, such that substitution happens to the right
-- as it does in case alternatives. Only first variable that matches predicate is
-- instantiated.
instClause :: MonadCatch m => VarSet        -- vars in scope
                           -> (Var -> Bool) -- predicate to select var
                           -> CoreExpr      -- expression to instantiate with
                           -> Clause -> m Clause
instClause inScope p e = prefixFailMsg "clause instantiation failed: " . liftM fst . go []
    where
          go bs (Forall b cl)
            | p b = do -- quantified here, so do substitution and start bubbling up
                let (eTvs, eTy) = splitForAllTys $ exprKindOrType e
                    tyVars = eTvs ++ filter isTyVar bs
                    failMsg = fail "type of provided expression differs from selected binder."

                    bindFn v = if v `elem` tyVars then BindMe else Skolem

                sub <- maybe failMsg return $ tcUnifyTys bindFn [varType b] [eTy]

                    -- if b is a tyvar, we know e is a type, so free vars will be tyvars
                let e' = mkCoreApps e [ case lookupTyVar sub v of
                                            Nothing -> Type (mkTyVarTy v)
                                            Just ty -> Type ty
                                      | v <- eTvs ]
                    cl' = substClause b e' cl
                    newBs = nonDetEltsUniqSet --varSetElems
                          $ filterVarSet (\v -> not (isId v) || isLocalId v)
                          $ delVarSetList (minusVarSet (freeVarsExpr e') inScope) bs

                return (replaceVars sub newBs cl', sub)
            | otherwise = do
                (cl', sub) <- go (b:bs) cl
                return (replaceVars sub [b] cl', sub)
          go bs (Conj    q1 q2) = go2 bs Conj      q1 q2
          go bs (Disj    q1 q2) = go2 bs Disj      q1 q2
          go bs (Impl nm q1 q2) = go2 bs (Impl nm) q1 q2
          go _ _ = fail "specified variable is not universally quantified."

          go2 bs con q1 q2 = do
            er <- attemptM $ go bs q1
            case er of
                Right (q1',s) -> return (con q1' q2, s)
                Left (_ :: SomeException) -> do
                    er' <- attemptM $ go bs q2
                    case er' of
                        Right (q2',s) -> return (con q1 q2', s)
                        Left (msg :: SomeException) -> fail (show msg) --(show msg)

-- | The function which 'bubbles up' after the instantiation takes place,
-- replacing any type variables that were instantiated as a result of specialization
-- and rebuilding the foralls.
#if __GLASGOW_HASKELL__ > 710
replaceVars :: TCvSubst -> [Var] -> Clause -> Clause
#else
replaceVars :: TvSubst -> [Var] -> Clause -> Clause
#endif
replaceVars sub vs = go (reverse vs)
    where go [] cl = cl
          go (b:bs) cl
            | isTyVar b = case lookupTyVar sub b of
                            Nothing -> go bs (addBinder b cl)
                            Just ty -> let new = nonDetEltsUniqSet(freeVarsType ty)
                                       in go (new++bs) (substClause b (Type ty) cl)
            | otherwise = go bs (addBinder b cl)

-- tvSubstToSubst :: TvSubst -> Subst
-- tvSubstToSubst (TvSubst inS tEnv) = mkSubst inS tEnv emptyVarEnv emptyVarEnv

-- | Instantiate a set of universally quantified variables in a 'Clause'.
-- It is important that all type variables appear before any value-level variables in the first argument.
instsClause :: MonadCatch m => VarSet -> [(Var,CoreExpr)] -> Clause -> m Clause
instsClause inScope = flip (foldM (\ q (v,e) -> instClause inScope (==v) e q)) . reverse
-- foldM is a left-to-right fold, so the reverse is important to do substitutions in reverse order
-- which is what we want (all value variables should be instantiated before type variables).

------------------------------------------------------------------------------

-- Syntactic Equality

-- | Syntactic Equality of clauses.
clauseSyntaxEq :: Clause -> Clause -> Bool
clauseSyntaxEq (Forall b1 c1)   (Forall b2 c2)  = (b1 == b2) && clauseSyntaxEq c1 c2
clauseSyntaxEq (Conj q1 q2)     (Conj p1 p2)    = clauseSyntaxEq q1 p1 && clauseSyntaxEq q2 p2
clauseSyntaxEq (Disj q1 q2)     (Disj p1 p2)    = clauseSyntaxEq q1 p1 && clauseSyntaxEq q2 p2
clauseSyntaxEq (Impl n1 q1 q2)  (Impl n2 p1 p2) = n1 == n2 && clauseSyntaxEq q1 p1 && clauseSyntaxEq q2 p2
clauseSyntaxEq (Equiv e1 e2)    (Equiv e1' e2') = exprSyntaxEq e1 e1'      && exprSyntaxEq e2 e2'
clauseSyntaxEq _                _               = False

------------------------------------------------------------------------------
