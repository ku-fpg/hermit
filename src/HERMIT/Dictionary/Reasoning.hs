{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, FlexibleInstances, InstanceSigs, ScopedTypeVariables #-}

module HERMIT.Dictionary.Reasoning
  ( -- * Equational Reasoning
    externals
  , CoreExprEquality(..)
  , CoreExprEqualityProof
  , eqLhsIntroR
  , eqRhsIntroR
  , birewrite
  , verifyCoreExprEqualityT
  , verifyEqualityLeftToRightT
  , verifyEqualityCommonTargetT
  , verifyIsomorphismT
  , verifyRetractionT
  , retractionBR
  , instantiateCoreExprEq
  )
where

import Control.Applicative
import Control.Arrow

import Data.Monoid

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.ParserCore
import HERMIT.Utilities

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Fold hiding (externals)
import HERMIT.Dictionary.Local.Let (nonRecIntroR)
import HERMIT.Dictionary.Unfold hiding (externals)

------------------------------------------------------------------------------

externals :: [External]
externals =
  [ external "retraction" ((\ f g r -> promoteExprBiR $ retraction (Just r) f g) :: CoreString -> CoreString -> RewriteH Core -> BiRewriteH Core)
        [ "Given f :: X -> Y and g :: Y -> X, and a proof that f (g y) ==> y, then"
        , "f (g y) <==> y."
        ] .+ Shallow
  , external "retraction-unsafe" ((\ f g -> promoteExprBiR $ retraction Nothing f g) :: CoreString -> CoreString -> BiRewriteH Core)
        [ "Given f :: X -> Y and g :: Y -> X, then"
        , "f (g y) <==> y."
        , "Note that the precondition (f (g y) == y) is expected to hold."
        ] .+ Shallow .+ PreCondition
  ]

------------------------------------------------------------------------------

-- | An equality is represented as a set of universally quantified binders, and then the LHS and RHS of the equality.
data CoreExprEquality = CoreExprEquality [CoreBndr] CoreExpr CoreExpr

type CoreExprEqualityProof c m = (Rewrite c m CoreExpr, Rewrite c m CoreExpr)

-- | @e@ ==> @let v = lhs in e@
eqLhsIntroR :: CoreExprEquality -> Rewrite c HermitM Core
eqLhsIntroR (CoreExprEquality bs lhs _) = nonRecIntroR "lhs" (mkCoreLams bs lhs)

-- | @e@ ==> @let v = rhs in e@
eqRhsIntroR :: CoreExprEquality -> Rewrite c HermitM Core
eqRhsIntroR (CoreExprEquality bs _ rhs) = nonRecIntroR "rhs" (mkCoreLams bs rhs)

------------------------------------------------------------------------------

-- | Create a 'BiRewrite' from a 'CoreExprEquality'.
--
-- The high level idea: create a temporary function with two definitions.
-- Fold one of the defintions, then immediately unfold the other.
birewrite :: (AddBindings c, ReadBindings c, ExtendPath c Crumb, ReadPath c Crumb) => CoreExprEquality -> BiRewrite c HermitM CoreExpr
birewrite (CoreExprEquality bnds l r) = bidirectional (foldUnfold l r) (foldUnfold r l)
    where foldUnfold lhs rhs = translate $ \ c e -> do
            let lhsLam = mkCoreLams bnds lhs
            -- we use a unique, transitory variable for the 'function' we are folding
            v <- newIdH "biTemp" (exprType lhsLam)
            e' <- maybe (fail "folding LHS failed") return (fold v lhsLam e)
            let rhsLam = mkCoreLams bnds rhs
                -- create a temporary context with an unfolding for the
                -- transitory function so we can reuse unfoldR.
                c' = addHermitBindings [(v, NONREC rhsLam, mempty)] c
            apply unfoldR c' e'

-- Idea: use Haskell's functions to fill the holes automagically
--
-- plusId <- findIdT "+"
-- timesId <- findIdT "*"
-- mkEquality $ \ x -> ( mkCoreApps (Var plusId)  [x,x]
--                     , mkCoreApps (Var timesId) [Lit 2, x])
--
-- Problem: need to know type of 'x' to generate a variable.
class BuildEquality a where
    mkEquality :: a -> HermitM CoreExprEquality

instance BuildEquality (CoreExpr,CoreExpr) where
    mkEquality :: (CoreExpr,CoreExpr) -> HermitM CoreExprEquality
    mkEquality (lhs,rhs) = return $ CoreExprEquality [] lhs rhs

instance BuildEquality a => BuildEquality (CoreExpr -> a) where
    mkEquality :: (CoreExpr -> a) -> HermitM CoreExprEquality
    mkEquality f = do
        x <- newIdH "x" (error "need to create a type")
        CoreExprEquality bnds lhs rhs <- mkEquality (f (varToCoreExpr x))
        return $ CoreExprEquality (x:bnds) lhs rhs

-- | Verify that a 'CoreExprEquality' holds, by applying a rewrite to each side, and checking that the results are equal.
verifyCoreExprEqualityT :: forall c m. (ReadPath c Crumb, MonadCatch m, Walker c Core) => CoreExprEqualityProof c m -> Translate c m CoreExprEquality ()
verifyCoreExprEqualityT (lhsR,rhsR) =
     do CoreExprEquality bs lhs rhs <- idR
        let lhsWithLams = mkCoreLams bs lhs
            rhsWithLams = mkCoreLams bs rhs
            path        = replicate (length bs) Lam_Body
        verifyEqualityCommonTargetT lhsWithLams rhsWithLams (coreExprPathR path lhsR, coreExprPathR path rhsR)
  where
    coreExprPathR :: Path Crumb -> Rewrite c m CoreExpr -> Rewrite c m CoreExpr
    coreExprPathR p r = extractR (pathR p (promoteExprR r :: Rewrite c m Core))

------------------------------------------------------------------------------

-- | Given two expressions, and a rewrite from the former to the latter, verify that rewrite.
verifyEqualityLeftToRightT :: MonadCatch m => CoreExpr -> CoreExpr -> Rewrite c m CoreExpr -> Translate c m a ()
verifyEqualityLeftToRightT sourceExpr targetExpr r =
  prefixFailMsg "equality verification failed: " $
  do resultExpr <- r <<< return sourceExpr
     guardMsg (exprAlphaEq targetExpr resultExpr) "result of running proof on lhs of equality does not match rhs of equality."

-- | Given two expressions, and a rewrite to apply to each, verify that the resulting expressions are equal.
verifyEqualityCommonTargetT :: MonadCatch m => CoreExpr -> CoreExpr -> CoreExprEqualityProof c m -> Translate c m a ()
verifyEqualityCommonTargetT lhs rhs (lhsR,rhsR) =
  prefixFailMsg "equality verification failed: " $
  do lhsResult <- lhsR <<< return lhs
     rhsResult <- rhsR <<< return rhs
     guardMsg (exprAlphaEq lhsResult rhsResult) "results of running proofs on both sides of equality do not match."

------------------------------------------------------------------------------

-- Note: We use global Ids for verification to avoid out-of-scope errors.

-- | Given f :: X -> Y and g :: Y -> X, verify that f (g y) ==> y and g (f x) ==> x.
verifyIsomorphismT :: CoreExpr -> CoreExpr -> Rewrite c HermitM CoreExpr -> Rewrite c HermitM CoreExpr -> Translate c HermitM a ()
verifyIsomorphismT f g fgR gfR = prefixFailMsg "Isomorphism verification failed: " $
   do (tyX, tyY) <- funsWithInverseTypes f g
      x          <- constT (newGlobalIdH "x" tyX)
      y          <- constT (newGlobalIdH "y" tyY)
      verifyEqualityLeftToRightT (App f (App g (Var y))) (Var y) fgR
      verifyEqualityLeftToRightT (App g (App f (Var x))) (Var x) gfR

-- | Given f :: X -> Y and g :: Y -> X, verify that f (g y) ==> y.
verifyRetractionT :: CoreExpr -> CoreExpr -> Rewrite c HermitM CoreExpr -> Translate c HermitM a ()
verifyRetractionT f g r = prefixFailMsg "Retraction verification failed: " $
   do (_tyX, tyY) <- funsWithInverseTypes f g
      y           <- constT (newGlobalIdH "y" tyY)
      let lhs = App f (App g (Var y))
          rhs = Var y
      verifyEqualityLeftToRightT lhs rhs r

------------------------------------------------------------------------------

-- | Given f :: X -> Y and g :: Y -> X, and a proof that f (g y) ==> y, then f (g y) <==> y.
retractionBR :: forall c. Maybe (Rewrite c HermitM CoreExpr) -> CoreExpr -> CoreExpr -> BiRewrite c HermitM CoreExpr
retractionBR mr f g = beforeBiR
                         (prefixFailMsg "Retraction failed: " $
                          do whenJust (verifyRetractionT f g) mr
                             y        <- idR
                             (_, tyY) <- funsWithInverseTypes f g
                             guardMsg (exprKindOrType y `typeAlphaEq` tyY) "type of expression does not match given retraction components."
                             return y
                         )
                         (\ y -> bidirectional
                                   retractionL
                                   (return $ App f (App g y))
                         )
  where
    retractionL :: Rewrite c HermitM CoreExpr
    retractionL =  prefixFailMsg "Retraction failed: " $
                   withPatFailMsg (wrongExprForm "App f (App g y)") $
      do App f' (App g' y) <- idR
         guardMsg (exprAlphaEq f f' && exprAlphaEq g g') "given retraction components do not match current expression."
         return y

-- | Given @f :: X -> Y@ and @g :: Y -> X@, and a proof that @f (g y)@ ==> @y@, then @f (g y)@ <==> @y@.
retraction :: Maybe (RewriteH Core) -> CoreString -> CoreString -> BiRewriteH CoreExpr
retraction mr = parse2beforeBiR (retractionBR (extractR <$> mr))

------------------------------------------------------------------------------

-- | Instantiate one of the universally quantified variables in a 'CoreExprEquality'.
-- Note: assumes implicit ordering of variables, such that substitution happens to the right
-- as it does in case alternatives.
instantiateCoreExprEqVar :: Var -> CoreExpr -> CoreExprEquality -> CoreExprEquality
instantiateCoreExprEqVar i e c@(CoreExprEquality bs lhs rhs) 
    | i `notElem` bs = c
    | otherwise = 
        let (bs',_:vs)    = break (==i) bs -- this is safe because we know i is in bs
            inS           = delVarSet (unionVarSets (map localFreeVarsExpr [lhs, rhs, e] ++ map freeVarsVar vs)) i
            subst         = extendSubst (mkEmptySubst (mkInScopeSet inS)) i e
            (subst', vs') = substBndrs subst vs
            lhs'          = substExpr (text "coreExprEquality-lhs") subst' lhs
            rhs'          = substExpr (text "coreExprEquality-rhs") subst' rhs
        in CoreExprEquality (bs'++vs') lhs' rhs'

-- | Instantiate a set of universally quantified variables in a 'CoreExprEquality'.
-- It is important that all type variables appear before any value-level variables in the first argument.
instantiateCoreExprEq :: [(Var,CoreExpr)] -> CoreExprEquality -> CoreExprEquality
instantiateCoreExprEq = flip (foldr (uncurry instantiateCoreExprEqVar))
-- foldr is important here because it effectively does the substitutions in reverse order, 
-- which is what we want (all value variables should be instantiated before type variables).

------------------------------------------------------------------------------
