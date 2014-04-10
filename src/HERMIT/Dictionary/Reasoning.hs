{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, FlexibleInstances, InstanceSigs, ScopedTypeVariables #-}

module HERMIT.Dictionary.Reasoning
  ( -- * Equational Reasoning
    externals
  , CoreExprEquality(..)
  , CoreExprEqualityProof
  , flipCoreExprEquality
  , eqLhsIntroR
  , eqRhsIntroR
  , birewrite
    -- ** Lifting transformations over 'CoreExprEquality'
  , lhsT
  , rhsT
  , bothT
  , lhsR
  , rhsR
  , bothR
  , proveCoreExprEqualityT
  , verifyCoreExprEqualityT
  , verifyEqualityLeftToRightT
  , verifyEqualityCommonTargetT
  , verifyIsomorphismT
  , verifyRetractionT
  , retractionBR
  , instantiateCoreExprEq
  , instantiateCoreExprEqVar
  , discardUniVars
  )
where

import Control.Applicative
import Control.Arrow
import Control.Monad

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

-- | Flip the LHS and RHS of a 'CoreExprEquality'.
flipCoreExprEquality :: CoreExprEquality -> CoreExprEquality
flipCoreExprEquality (CoreExprEquality xs lhs rhs) = CoreExprEquality xs rhs lhs

------------------------------------------------------------------------------

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
birewrite :: (AddBindings c, ReadBindings c, ExtendPath c Crumb, ReadPath c Crumb, HasEmptyContext c) => CoreExprEquality -> BiRewrite c HermitM CoreExpr
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

-- | Lift a transformation over 'CoreExpr' into a transformation over the left-hand side of a 'CoreExprEquality'.
lhsT :: (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadPath c Crumb, MonadCatch m) => Translate c m CoreExpr b -> Translate c m CoreExprEquality b
lhsT t = idR >>= \ (CoreExprEquality vs lhs _) -> return lhs >>> withVarsInScope vs t

-- | Lift a transformation over 'CoreExpr' into a transformation over the right-hand side of a 'CoreExprEquality'.
rhsT :: (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadPath c Crumb, MonadCatch m) => Translate c m CoreExpr b -> Translate c m CoreExprEquality b
rhsT t = idR >>= \ (CoreExprEquality vs _ rhs) -> return rhs >>> withVarsInScope vs t

-- | Lift a transformation over 'CoreExpr' into a transformation over both sides of a 'CoreExprEquality'.
bothT :: (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadPath c Crumb, MonadCatch m) => Translate c m CoreExpr b -> Translate c m CoreExprEquality (b,b)
bothT t = liftM2 (,) (lhsT t) (rhsT t) -- Can't wait for Applicative to be a superclass of Monad

-- | Lift a rewrite over 'CoreExpr' into a rewrite over the left-hand side of a 'CoreExprEquality'.
lhsR :: (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadPath c Crumb, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m CoreExprEquality
lhsR r = do
    CoreExprEquality vs lhs rhs <- idR
    lhs' <- withVarsInScope vs r <<< return lhs
    return $ CoreExprEquality vs lhs' rhs

-- | Lift a rewrite over 'CoreExpr' into a rewrite over the right-hand side of a 'CoreExprEquality'.
rhsR :: (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadPath c Crumb, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m CoreExprEquality
rhsR r = do
    CoreExprEquality vs lhs rhs <- idR
    rhs' <- withVarsInScope vs r <<< return rhs
    return $ CoreExprEquality vs lhs rhs'

-- | Lift a rewrite over 'CoreExpr' into a rewrite over both sides of a 'CoreExprEquality'.
bothR :: (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadPath c Crumb, MonadCatch m) => Rewrite c m CoreExpr -> Rewrite c m CoreExprEquality
bothR r = lhsR r >>> rhsR r

------------------------------------------------------------------------------

-- Idea: use Haskell's functions to fill the holes automagically
--
-- plusId <- findIdT "+"
-- timesId <- findIdT "*"
-- mkEquality $ \ x -> ( mkCoreApps (Var plusId)  [x,x]
--                     , mkCoreApps (Var timesId) [Lit 2, x])
--
-- TODO: need to know type of 'x' to generate a variable.
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

------------------------------------------------------------------------------

-- | Verify that a 'CoreExprEquality' holds, by applying a rewrite to each side, and checking that the results are equal.
proveCoreExprEqualityT :: forall c m. (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, HasEmptyContext c, MonadCatch m, Walker c Core) 
                        => CoreExprEqualityProof c m -> Translate c m CoreExprEquality ()
proveCoreExprEqualityT (l,r) = lhsR l >>> rhsR r >>> verifyCoreExprEqualityT

-- | Verify that the left- and right-hand sides of a 'CoreExprEquality' are alpha equivalent.
verifyCoreExprEqualityT :: Monad m => Translate c m CoreExprEquality ()
verifyCoreExprEqualityT = do
    CoreExprEquality _ lhs rhs <- idR
    guardMsg (exprAlphaEq lhs rhs) "the two sides of the equality do not match."

------------------------------------------------------------------------------

-- TODO: are these other functions used? If so, can they be rewritten in terms of lhsR and rhsR as above?

-- | Given two expressions, and a rewrite from the former to the latter, verify that rewrite.
verifyEqualityLeftToRightT :: MonadCatch m => CoreExpr -> CoreExpr -> Rewrite c m CoreExpr -> Translate c m a ()
verifyEqualityLeftToRightT sourceExpr targetExpr r =
  prefixFailMsg "equality verification failed: " $
  do resultExpr <- r <<< return sourceExpr
     guardMsg (exprAlphaEq targetExpr resultExpr) "result of running proof on lhs of equality does not match rhs of equality."

-- | Given two expressions, and a rewrite to apply to each, verify that the resulting expressions are equal.
verifyEqualityCommonTargetT :: MonadCatch m => CoreExpr -> CoreExpr -> CoreExprEqualityProof c m -> Translate c m a ()
verifyEqualityCommonTargetT lhs rhs (l,r) =
  prefixFailMsg "equality verification failed: " $
  do lhsResult <- l <<< return lhs
     rhsResult <- r <<< return rhs
     guardMsg (exprAlphaEq lhsResult rhsResult) "results of running proofs on both sides of equality do not match."

------------------------------------------------------------------------------

-- Note: We use global Ids for verification to avoid out-of-scope errors.

-- | Given f :: X -> Y and g :: Y -> X, verify that f (g y) ==> y and g (f x) ==> x.
verifyIsomorphismT :: CoreExpr -> CoreExpr -> Rewrite c HermitM CoreExpr -> Rewrite c HermitM CoreExpr -> Translate c HermitM a ()
verifyIsomorphismT f g fgR gfR = prefixFailMsg "Isomorphism verification failed: " $
   do (tyX, tyY) <- funExprsWithInverseTypes f g
      x          <- constT (newGlobalIdH "x" tyX)
      y          <- constT (newGlobalIdH "y" tyY)
      verifyEqualityLeftToRightT (App f (App g (Var y))) (Var y) fgR
      verifyEqualityLeftToRightT (App g (App f (Var x))) (Var x) gfR

-- | Given f :: X -> Y and g :: Y -> X, verify that f (g y) ==> y.
verifyRetractionT :: CoreExpr -> CoreExpr -> Rewrite c HermitM CoreExpr -> Translate c HermitM a ()
verifyRetractionT f g r = prefixFailMsg "Retraction verification failed: " $
   do (_tyX, tyY) <- funExprsWithInverseTypes f g
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
                             (_, tyY) <- funExprsWithInverseTypes f g
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
            inS           = delVarSetList (unionVarSets (map localFreeVarsExpr [lhs, rhs, e] ++ map freeVarsVar vs)) (i:vs)
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

discardUniVars :: CoreExprEquality -> CoreExprEquality
discardUniVars (CoreExprEquality _ lhs rhs) = CoreExprEquality [] lhs rhs
