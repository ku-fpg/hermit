{-# LANGUAGE ScopedTypeVariables #-}

module HERMIT.Primitive.FixPoint
       ( -- * Operations on the Fixed Point Operator (fix)
         -- | Note that many of these operations require 'Data.Function.fix' to be in scope.
         HERMIT.Primitive.FixPoint.externals
         -- ** Rewrites and BiRewrites on Fixed Points
       , fixIntroR
       , fixComputationRuleBR
       , fixRollingRuleBR
       , fixFusionRuleBR
         -- ** Utilities
       , mkFixT
       , isFixExprT
       )
where

import Control.Applicative
import Control.Arrow

import Data.Monoid (mempty)

import HERMIT.Context
import HERMIT.Core
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC
import HERMIT.ParserCore
import HERMIT.Utilities

import HERMIT.Primitive.Common
import HERMIT.Primitive.GHC
import HERMIT.Primitive.Undefined

import qualified Language.Haskell.TH as TH

--------------------------------------------------------------------------------------------------

-- | Externals for manipulating fixed points.
externals ::  [External]
externals =
         [ external "fix-intro" (promoteDefR fixIntroR :: RewriteH Core)
                [ "rewrite a recursive binding into a non-recursive binding using fix"
                ] .+ Introduce .+ Context
         , external "fix-computation-rule" (promoteExprBiR fixComputationRuleBR :: BiRewriteH Core)
                [ "Fixed-Point Computation Rule",
                  "fix t f  <==>  f (fix t f)"
                ] .+ Context
         , external "fix-rolling-rule" (promoteExprBiR fixRollingRuleBR :: BiRewriteH Core)
                [ "Rolling Rule",
                  "fix tyA (\\ a -> f (g a))  <==>  f (fix tyB (\\ b -> g (f b))"
                ] .+ Context
         , external "fix-fusion-rule" ((\ f g h lhsR rhsR strictf -> promoteExprBiR (fixFusionRule (Just (lhsR,rhsR)) (Just strictf) f g h)) :: CoreString -> CoreString -> CoreString -> RewriteH Core -> RewriteH Core -> RewriteH Core -> BiRewriteH Core)
                [ "Fixed-point Fusion Rule"
                , "Given f :: A -> B, g :: A -> A, h :: B -> B, and"
                , "proofs that, for some x, (f (g a) ==> x) and (h (f a) ==> x) and that f is strict, then"
                , "f (fix g) <==> fix h"
                ] .+ Context
         , external "fix-fusion-rule-unsafe" ((\ f g h lhsR rhsR -> promoteExprBiR (fixFusionRule (Just (lhsR,rhsR)) Nothing f g h)) :: CoreString -> CoreString -> CoreString -> RewriteH Core -> RewriteH Core -> BiRewriteH Core)
                [ "(Unsafe) Fixed-point Fusion Rule"
                , "Given f :: A -> B, g :: A -> A, h :: B -> B, and"
                , "a proof that, for some x, (f (g a) ==> x) and (h (f a) ==> x), then"
                , "f (fix g) <==> fix h"
                , "Note that the precondition that f is strict is required to hold."
                ] .+ Context .+ PreCondition
         , external "fix-fusion-rule-unsafe" ((\ f g h -> promoteExprBiR (fixFusionRule Nothing Nothing f g h)) :: CoreString -> CoreString -> CoreString -> BiRewriteH Core)
                [ "(Very Unsafe) Fixed-point Fusion Rule"
                , "Given f :: A -> B, g :: A -> A, h :: B -> B, then"
                , "f (fix g) <==> fix h"
                , "Note that the preconditions that f (g a) == h (f a) and that f is strict are required to hold."
                ] .+ Context .+ PreCondition
         ]

--------------------------------------------------------------------------------------------------

-- |  @f = e@   ==\>   @f = fix (\\ f -> e)@
fixIntroR :: RewriteH CoreDef
fixIntroR = prefixFailMsg "fix introduction failed: " $
           do Def f _ <- idR
              f' <- constT $ cloneVarH id f
              Def f <$> (mkFixT =<< (defT mempty (extractR $ substR f $ varToCoreExpr f') (\ () e' -> Lam f' e')))

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
                      (tyA',tyB) <- funsWithInverseTypes g f
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
                           (tyA,tyB') <- funsWithInverseTypes g f
                           guardMsg (eqType tyB tyB') "Type mismatch: this shouldn't have happened, report this as a bug."
                           rollingRuleResult tyA f g

    rollingRuleResult :: Type -> CoreExpr -> CoreExpr -> TranslateH z CoreExpr
    rollingRuleResult ty f g = do x <- constT (newIdH "x" ty)
                                  mkFixT (Lam x (App f (App g (Var x))))

    wrongFixBody :: String
    wrongFixBody = "body of fix does not have the form: Lam v (App f (App g (Var v)))"

--------------------------------------------------------------------------------------------------

-- f :: A -> B
-- g :: A -> A
-- h :: B -> B

-- | If @f@ is strict, then (@f (g a)@ == @h (f a)@)  ==\>  (@f (fix g)@ == @fix h@)
fixFusionRuleBR :: Maybe (RewriteH CoreExpr, RewriteH CoreExpr) -> Maybe (RewriteH CoreExpr) -> CoreExpr -> CoreExpr -> CoreExpr -> BiRewriteH CoreExpr
fixFusionRuleBR meq mfstrict f g h = beforeBiR
  (prefixFailMsg "fixed-point fusion failed: " $
   do (tyA,tyB) <- funArgResTypes f
      tyA'      <- endoFunType g
      tyB'      <- endoFunType h
      guardMsg (typeAlphaEq tyA tyA' && typeAlphaEq tyB tyB') "given functions do not have compatible types."
      whenJust (verifyStrictT f) mfstrict
      whenJust (\ (lhsR,rhsR) ->
                  do a <- constT (newIdH "a" tyA)
                     let lhs = App f (App g (Var a))
                         rhs = App h (App f (Var a))
                     verifyEqualityCommonTargetT lhs rhs lhsR rhsR
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
                       mkFixT h

       fixFusionR :: RewriteH CoreExpr
       fixFusionR = prefixFailMsg "(reversed) fixed-point fusion failed: " $
                    do (_,h') <- isFixExprT
                       guardMsg (exprAlphaEq h h') "third argument function does not match."
                       App f <$> mkFixT g

-- | If @f@ is strict, then (@f (g a)@ == @h (f a)@)  ==>  (@f (fix g)@ == @fix h@)
fixFusionRule :: Maybe (RewriteH Core, RewriteH Core) -> Maybe (RewriteH Core) -> CoreString -> CoreString -> CoreString -> BiRewriteH CoreExpr
fixFusionRule meq mfstrict = parse3beforeBiR $ fixFusionRuleBR ((extractR *** extractR) <$> meq) (extractR <$> mfstrict)

--------------------------------------------------------------------------------------------------

-- | Check that the expression has the form "fix t (f :: t -> t)", returning "t" and "f".
isFixExprT :: TranslateH CoreExpr (Type,CoreExpr)
isFixExprT = withPatFailMsg (wrongExprForm "fix t f") $ -- fix :: forall a. (a -> a) -> a
  do App (App (Var fixId) (Type ty)) f <- idR
     fixId' <- findFixId
     guardMsg (fixId == fixId') (var2String fixId ++ " does not match " ++ fixLocation)
     return (ty,f)

--------------------------------------------------------------------------------------------------

-- | f  ==>  fix f
mkFixT :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => CoreExpr -> Translate c m z CoreExpr
mkFixT f = do t <- endoFunType f
              fixId <- findFixId
              return $ mkCoreApps (varToCoreExpr fixId) [Type t, f]

fixLocation :: String
fixLocation = "Data.Function.fix"

-- TODO: will crash if 'fix' is not used (or explicitly imported) in the source file.
findFixId :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Translate c m a Id
findFixId = findIdT (TH.mkName fixLocation)

--------------------------------------------------------------------------------------------------
