{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Dictionary.FixPoint
    ( -- * Operations on the Fixed Point Operator (fix)
      HERMIT.Dictionary.FixPoint.externals
      -- ** Rewrites and BiRewrites on Fixed Points
    , fixIntroR
    , fixIntroNonRecR
    , fixIntroRecR
    , fixComputationRuleBR
    , fixRollingRuleBR
    , fixFusionRuleBR
      -- ** Utilities
    , isFixExprT
    ) where

import Control.Arrow
import Control.Monad
import Control.Monad.IO.Class

import Data.String (fromString)

import HERMIT.Context
import HERMIT.Core
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC
import HERMIT.Name
import HERMIT.ParserCore
import HERMIT.Utilities

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Function
import HERMIT.Dictionary.Kure
import HERMIT.Dictionary.Reasoning
import HERMIT.Dictionary.Undefined
import HERMIT.Dictionary.Unfold

--------------------------------------------------------------------------------------------------

-- | Externals for manipulating fixed points.
externals ::  [External]
externals =
    [ external "fix-intro" (fixIntroR :: RewriteH Core)
        [ "rewrite a function binding into a non-recursive binding using fix" ] .+ Introduce .+ Context
    , external "fix-computation-rule" (promoteExprBiR fixComputationRuleBR :: BiRewriteH Core)
        [ "Fixed-Point Computation Rule",
          "fix t f  <==>  f (fix t f)"
        ] .+ Context
    , external "fix-rolling-rule" (promoteExprBiR fixRollingRuleBR :: BiRewriteH Core)
        [ "Rolling Rule",
          "fix tyA (\\ a -> f (g a))  <==>  f (fix tyB (\\ b -> g (f b))"
        ] .+ Context
    , external "fix-fusion-rule" ((\ f g h r1 r2 strictf -> promoteExprBiR
                                                                (fixFusionRule (Just (r1,r2)) (Just strictf) f g h))
                                                                :: CoreString -> CoreString -> CoreString
                                                                    -> RewriteH Core -> RewriteH Core
                                                                    -> RewriteH Core -> BiRewriteH Core)
        [ "Fixed-point Fusion Rule"
        , "Given f :: A -> B, g :: A -> A, h :: B -> B, and"
        , "proofs that, for some x, (f (g a) ==> x) and (h (f a) ==> x) and that f is strict, then"
        , "f (fix g) <==> fix h"
        ] .+ Context
    , external "fix-fusion-rule-unsafe" ((\ f g h r1 r2 -> promoteExprBiR (fixFusionRule (Just (r1,r2)) Nothing f g h))
                                                            :: CoreString -> CoreString -> CoreString
                                                                -> RewriteH Core -> RewriteH Core -> BiRewriteH Core)
        [ "(Unsafe) Fixed-point Fusion Rule"
        , "Given f :: A -> B, g :: A -> A, h :: B -> B, and"
        , "a proof that, for some x, (f (g a) ==> x) and (h (f a) ==> x), then"
        , "f (fix g) <==> fix h"
        , "Note that the precondition that f is strict is required to hold."
        ] .+ Context .+ PreCondition
    , external "fix-fusion-rule-unsafe" ((\ f g h -> promoteExprBiR (fixFusionRule Nothing Nothing f g h))
                                                        :: CoreString -> CoreString -> CoreString -> BiRewriteH Core)
        [ "(Very Unsafe) Fixed-point Fusion Rule"
        , "Given f :: A -> B, g :: A -> A, h :: B -> B, then"
        , "f (fix g) <==> fix h"
        , "Note that the preconditions that f (g a) == h (f a) and that f is strict are required to hold."
        ] .+ Context .+ PreCondition
    ]

--------------------------------------------------------------------------------------------------

fixIntroR :: ( AddBindings c, BoundVars c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
             , HasHermitMEnv m, HasHscEnv m, MonadCatch m, MonadIO m, MonadThings m, MonadUnique m )
          => Rewrite c m Core
fixIntroR = promoteR fixIntroRecR <+ promoteR fixIntroNonRecR

fixIntroNonRecR :: ( AddBindings c, BoundVars c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
                   , HasHermitMEnv m, HasHscEnv m, MonadCatch m, MonadIO m, MonadThings m, MonadUnique m )
                => Rewrite c m CoreBind
fixIntroNonRecR = prefixFailMsg "fix introduction failed: " $ do
    NonRec f rhs <- idR
    rhs' <- polyFixT f <<< return rhs
    return $ NonRec f rhs'

-- |  @f = e@   ==\>   @f = fix (\\ f -> e)@
fixIntroRecR :: ( AddBindings c, BoundVars c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
                , HasHermitMEnv m, HasHscEnv m, MonadCatch m, MonadIO m, MonadThings m, MonadUnique m )
             => Rewrite c m CoreDef
fixIntroRecR = prefixFailMsg "fix introduction failed: " $ do
    Def f rhs <- idR
    rhs' <- polyFixT f <<< return rhs
    return $ Def f rhs'

-- | Helper for fixIntroNonRecR and fixIntroRecR. Argument is function name.
-- Meant to be applied to RHS of function.
polyFixT :: forall c m.
            ( AddBindings c, BoundVars c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
            , HasHermitMEnv m, HasHscEnv m, MonadCatch m, MonadIO m, MonadThings m, MonadUnique m )
         => Id -> Rewrite c m CoreExpr
polyFixT f = do
    (tvs, body) <- arr collectTyBinders
    f' <- constT $ newIdH (unqualifiedName f) (exprType body)
    body' <- contextonlyT $ \ c -> do
                let constLam = mkCoreLams tvs $ varToCoreExpr f'
                    c' = addBindingGroup (NonRec f constLam)   -- we want to unfold f such as to throw away TyArgs
                       $ addBindingGroup (NonRec f' body)    c -- add f' to context so its in-scope after unfolding
                applyT (tryR (extractR (anyCallR (promoteR (unfoldPredR (const . (==f))) :: Rewrite c m Core)))) c' body
    liftM (mkCoreLams tvs) $ buildFixT $ Lam f' body'

--------------------------------------------------------------------------------------------------

-- | @fix ty f@  \<==\>  @f (fix ty f)@
fixComputationRuleBR :: BiRewriteH CoreExpr
fixComputationRuleBR = bidirectional computationL computationR
  where
    computationL :: RewriteH CoreExpr
    computationL = prefixFailMsg "fix computation rule failed: " $
                   do (_,f) <- isFixExprT
                      fixf  <- idR
                      return (App f fixf)

    computationR :: RewriteH CoreExpr
    computationR = prefixFailMsg "(backwards) fix computation rule failed: " $
                   do App f fixf <- idR
                      (_,f') <- isFixExprT <<< constant fixf
                      guardMsg (exprAlphaEq f f') "external function does not match internal expression"
                      return fixf


-- | @fix tyA (\\ a -> f (g a))@  \<==\>  @f (fix tyB (\\ b -> g (f b))@
fixRollingRuleBR :: BiRewriteH CoreExpr
fixRollingRuleBR = bidirectional rollingRuleL rollingRuleR
  where
    rollingRuleL :: RewriteH CoreExpr
    rollingRuleL = prefixFailMsg "rolling rule failed: " $
                   withPatFailMsg wrongFixBody $
                   do (tyA, Lam a (App f (App g (Var a')))) <- isFixExprT
                      guardMsg (a == a') wrongFixBody
                      (tyA',tyB) <- funExprsWithInverseTypes g f
                      guardMsg (eqType tyA tyA') "Type mismatch: this shouldn't have happened, report this as a bug."
                      res <- rollingRuleResult tyB g f
                      return (App f res)

    rollingRuleR :: RewriteH CoreExpr
    rollingRuleR = prefixFailMsg "(reversed) rolling rule failed: " $
                   withPatFailMsg "not an application." $
                   do App f fx <- idR
                      withPatFailMsg wrongFixBody $
                        do (tyB, Lam b (App g (App f' (Var b')))) <- isFixExprT <<< constant fx
                           guardMsg (b == b') wrongFixBody
                           guardMsg (exprAlphaEq f f') "external function does not match internal expression"
                           (tyA,tyB') <- funExprsWithInverseTypes g f
                           guardMsg (eqType tyB tyB') "Type mismatch: this shouldn't have happened, report this as a bug."
                           rollingRuleResult tyA f g

    rollingRuleResult :: Type -> CoreExpr -> CoreExpr -> TransformH z CoreExpr
    rollingRuleResult ty f g = do x <- constT (newIdH "x" ty)
                                  buildFixT (Lam x (App f (App g (Var x))))

    wrongFixBody :: String
    wrongFixBody = "body of fix does not have the form: Lam v (App f (App g (Var v)))"

--------------------------------------------------------------------------------------------------

-- f :: A -> B
-- g :: A -> A
-- h :: B -> B

-- | If @f@ is strict, then (@f (g a)@ == @h (f a)@)  ==\>  (@f (fix g)@ == @fix h@)
fixFusionRuleBR :: Maybe (EqualityProof HermitC HermitM) -> Maybe (RewriteH CoreExpr) -> CoreExpr -> CoreExpr -> CoreExpr -> BiRewriteH CoreExpr
fixFusionRuleBR meq mfstrict f g h = beforeBiR
  (prefixFailMsg "fixed-point fusion failed: " $
   do (_,tyA,tyB) <- funExprArgResTypesM f -- TODO: don't throw away TyVars
      (_,tyA')    <- endoFunExprTypeM g
      (_,tyB')    <- endoFunExprTypeM h
      guardMsg (typeAlphaEq tyA tyA' && typeAlphaEq tyB tyB') "given functions do not have compatible types."
      whenJust (verifyStrictT f) mfstrict
      whenJust (\ eq ->
                  do a <- constT (newGlobalIdH "a" tyA)
                     let lhs = App f (App g (Var a))
                         rhs = App h (App f (Var a))
                     verifyEqualityCommonTargetT lhs rhs eq
               )
               meq
  )
  (\ () -> bidirectional fixFusionL fixFusionR)

     where
       fixFusionL :: RewriteH CoreExpr
       fixFusionL = prefixFailMsg "fixed-point fusion failed: " $
                    withPatFailMsg (wrongExprForm "App f (fix g)") $
                    do App f' fixg <- idR
                       guardMsg (exprAlphaEq f f') "first argument function does not match."
                       (_,g') <- isFixExprT <<< return fixg
                       guardMsg (exprAlphaEq g g') "second argument function does not match."
                       buildFixT h

       fixFusionR :: RewriteH CoreExpr
       fixFusionR = prefixFailMsg "(reversed) fixed-point fusion failed: " $
                    do (_,h') <- isFixExprT
                       guardMsg (exprAlphaEq h h') "third argument function does not match."
                       App f <$> buildFixT g

-- | If @f@ is strict, then (@f (g a)@ == @h (f a)@)  ==>  (@f (fix g)@ == @fix h@)
fixFusionRule :: Maybe (RewriteH Core, RewriteH Core) -> Maybe (RewriteH Core) -> CoreString -> CoreString -> CoreString -> BiRewriteH CoreExpr
fixFusionRule meq mfstrict = parse3beforeBiR $ fixFusionRuleBR ((extractR *** extractR) <$> meq) (extractR <$> mfstrict)

--------------------------------------------------------------------------------------------------

-- | Check that the expression has the form "fix t (f :: t -> t)", returning "t" and "f".
isFixExprT :: TransformH CoreExpr (Type,CoreExpr)
isFixExprT = withPatFailMsg (wrongExprForm "fix t f") $ -- fix :: forall a. (a -> a) -> a
  do (Var fixId, [Type ty, f]) <- callT
     fixId' <- findIdT fixLocation
     guardMsg (fixId == fixId') (unqualifiedName fixId ++ " does not match " ++ show fixLocation)
     return (ty,f)

--------------------------------------------------------------------------------------------------

fixLocation :: HermitName
fixLocation = fromString "Data.Function.fix"

--------------------------------------------------------------------------------------------------
