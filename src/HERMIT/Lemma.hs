{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE InstanceSigs #-}

module HERMIT.Lemma
    ( -- * Clause
      Clause(..)
    , mkClause
    , mkForall
    , forallQs
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

import Data.Dynamic (Typeable)
import Data.String (IsString(..))
import qualified Data.Map as M
#if __GLASGOW_HASKELL__ < 710
import Data.Monoid
#endif

import HERMIT.Core
import HERMIT.GHC hiding ((<>))
import Language.KURE.MonadCatch

----------------------------------------------------------------------------

-- | Build a Clause from a list of universally quantified binders and two expressions.
-- If the head of either expression is a lambda expression, it's binder will become a universally quantified binder
-- over both sides. It is assumed the two expressions have the same type.
--
-- Ex.    mkClause [] (\x. foo x) bar === forall x. foo x = bar x
--        mkClause [] (baz y z) (\x. foo x x) === forall x. baz y z x = foo x x
--        mkClause [] (\x. foo x) (\y. bar y) === forall x. foo x = bar x
mkClause :: [CoreBndr] -> CoreExpr -> CoreExpr -> Clause
mkClause vs lhs rhs = redundantDicts $ dropBinders $ Forall (tvs++vs++lbs++rbs) (Equiv lhs' rbody)
    where (lbs, lbody) = collectBinders lhs
          rhs' = uncurry mkCoreApps $ betaReduceAll rhs $ map varToCoreExpr lbs
          (rbs, rbody) = collectBinders rhs'
          lhs' = mkCoreApps lbody $ map varToCoreExpr rbs
          -- now quantify over the free type variables
          tvs = varSetElems
              $ filterVarSet isTyVar
              $ delVarSetList (unionVarSets $ map freeVarsExpr [lhs',rbody]) (vs++lbs++rbs)

freeVarsClause :: Clause -> VarSet
freeVarsClause (Forall bs cl) = delVarSetList (freeVarsClause cl) bs
freeVarsClause (Conj  q1 q2)  = unionVarSets $ map freeVarsClause [q1,q2]
freeVarsClause (Disj  q1 q2)  = unionVarSets $ map freeVarsClause [q1,q2]
freeVarsClause (Impl _ q1 q2) = unionVarSets $ map freeVarsClause [q1,q2]
freeVarsClause (Equiv e1 e2)  = unionVarSets $ map freeVarsExpr [e1,e2]
freeVarsClause CTrue          = emptyVarSet

dropBinders :: Clause -> Clause
dropBinders (Forall bs cl)  =
    case bs of
        []      -> dropBinders cl
        (b:bs') -> let c = dropBinders (mkForall bs' cl)
                   in if b `elemVarSet` freeVarsClause c
                      then addBinder b c
                      else c
dropBinders (Conj q1 q2)    = Conj (dropBinders q1) (dropBinders q2)
dropBinders (Disj q1 q2)    = Disj (dropBinders q1) (dropBinders q2)
dropBinders (Impl nm q1 q2) = Impl nm (dropBinders q1) (dropBinders q2)
dropBinders other           = other

addBinder :: CoreBndr -> Clause -> Clause
addBinder b = mkForall [b]

mkForall :: [CoreBndr] -> Clause -> Clause
mkForall bs (Forall bs' cl) = Forall (bs++bs') cl
mkForall bs cl              = Forall bs cl

forallQs :: Clause -> [CoreBndr]
forallQs (Forall bs _) = bs
forallQs _             = []

-- | A name for lemmas. Use a newtype so we can tab-complete in shell.
newtype LemmaName = LemmaName String deriving (Eq, Ord, Typeable)

instance Monoid LemmaName where
    mempty = LemmaName mempty
    mappend (LemmaName n1) (LemmaName n2) = LemmaName (mappend n1 n2)

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
    deriving (Eq, Typeable)

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
    deriving (Eq, Typeable)

instance Show Used where
    show Obligation = "Obligation"
    show UnsafeUsed = "Used"
    show NotUsed    = "Not Used"

data Clause = Forall [CoreBndr] Clause
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
discardUniVars (Forall _ cl) = cl
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
    where go sub (Forall bs cl) =
            let (bs', cl') = go1 sub bs [] cl
            in mkForall bs' cl'
          go _     CTrue           = CTrue
          go subst (Conj q1 q2)    = Conj    (go subst q1) (go subst q2)
          go subst (Disj q1 q2)    = Disj    (go subst q1) (go subst q2)
          go subst (Impl nm q1 q2) = Impl nm (go subst q1) (go subst q2)
          go subst (Equiv e1 e2)   =
            let e1' = substExpr (text "substClauseSubst e1") subst e1
                e2' = substExpr (text "substClauseSubst e2") subst e2
            in Equiv e1' e2'

          go1 subst [] bs' cl = (reverse bs', go subst cl)
          go1 subst (b:bs) bs' cl =
            let (subst',b') = substBndr subst b
            in go1 subst' bs (b':bs') cl

------------------------------------------------------------------------------

redundantDicts :: Clause -> Clause
redundantDicts (Forall bs cl) = go [] [] cl bs
    where go []   _   c [] = c
          go bnds _   c [] = mkForall (reverse bnds) c
          go bnds tys c (b:bs')
              | isDictTy bTy = -- is a dictionary binder
                let match = [ varToCoreExpr pb | (pb,ty) <- tys , eqType bTy ty ]
                in if null match
                   then go (b:bnds) ((b,bTy):tys) c bs' -- not seen before
                   else let Forall bs'' c' = substClause b (head match) $ mkForall bs' c
                        in go bnds tys c' bs'' -- seen
              | otherwise = go (b:bnds) tys c bs'
            where bTy = varType b
redundantDicts cl             = cl

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
    where go bbs (Forall bs cl)
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
                        return (replaceVars s bs cl', s)
                in case cl of
                    Equiv{} -> fail "specified variable is not universally quantified."
                    CTrue   -> fail "specified variable is not universally quantified."
                    Conj q1 q2 -> go2 Conj q1 q2
                    Disj q1 q2 -> go2 Disj q1 q2
                    Impl nm q1 q2 -> go2 (Impl nm) q1 q2
                    Forall _ _ -> fail "impossible case!"

            | otherwise = do -- quantified here, so do substitution and start bubbling up
                let (bs',i:vs) = break p bs -- this is safe because we know i is in bs
                    (eTvs, eTy) = splitForAllTys $ exprKindOrType e
                    bsInScope = bs'++bbs
                    tyVars = eTvs ++ filter isTyVar bsInScope
                    failMsg = fail "type of provided expression differs from selected binder."

                    bindFn v = if v `elem` tyVars then BindMe else Skolem

                sub <- maybe failMsg return $ tcUnifyTys bindFn [varType i] [eTy]

                    -- if i is a tyvar, we know e is a type, so free vars will be tyvars
                let e' = mkCoreApps e [ case lookupTyVar sub v of
                                            Nothing -> Type (mkTyVarTy v)
                                            Just ty -> Type ty | v <- eTvs ]
                let newBs = varSetElems
                          $ filterVarSet (\v -> not (isId v) || isLocalId v)
                          $ delVarSetList (minusVarSet (freeVarsExpr e') inScope) bsInScope
                    cl' = substClause i e' $ mkForall vs cl

                return (replaceVars sub (bs' ++ newBs) cl', sub)
          go _ _ = fail "only applies to clauses with quantifiers."

-- | The function which 'bubbles up' after the instantiation takes place,
-- replacing any type variables that were instantiated as a result of specialization.
replaceVars :: TvSubst -> [Var] -> Clause -> Clause
replaceVars sub vs = go (reverse vs)
    where go [] cl = cl
          go (b:bs) cl
            | isTyVar b = case lookupTyVar sub b of
                            Nothing -> go bs (addBinder b cl)
                            Just ty -> let new = varSetElems (freeVarsType ty)
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
clauseSyntaxEq (Forall bs1 c1)  (Forall bs2 c2) = (bs1 == bs2) && clauseSyntaxEq c1 c2
clauseSyntaxEq (Conj q1 q2)     (Conj p1 p2)    = clauseSyntaxEq q1 p1 && clauseSyntaxEq q2 p2
clauseSyntaxEq (Disj q1 q2)     (Disj p1 p2)    = clauseSyntaxEq q1 p1 && clauseSyntaxEq q2 p2
clauseSyntaxEq (Impl n1 q1 q2)  (Impl n2 p1 p2) = n1 == n2 && clauseSyntaxEq q1 p1 && clauseSyntaxEq q2 p2
clauseSyntaxEq (Equiv e1 e2)    (Equiv e1' e2') = exprSyntaxEq e1 e1'      && exprSyntaxEq e2 e2'
clauseSyntaxEq _                _               = False

------------------------------------------------------------------------------
