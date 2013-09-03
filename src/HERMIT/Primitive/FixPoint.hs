module HERMIT.Primitive.FixPoint
       ( -- * Operations on the Fixed Point Operator (fix)
         -- | Note that many of these operations require 'Data.Function.fix' to be in scope.
         HERMIT.Primitive.FixPoint.externals
         -- ** Rewrites and BiRewrites on Fixed Points
       , fixIntro
       , fixComputationRule
       , rollingRule
         -- ** Utilities
       , mkFix
       , isFixExpr
       )
where

import Control.Applicative
import Control.Arrow

import Data.Monoid (mempty)

import HERMIT.Core
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC

import HERMIT.Primitive.Common
import HERMIT.Primitive.GHC

import qualified Language.Haskell.TH as TH

--------------------------------------------------------------------------------------------------

-- | Externals for manipulating fixed points.
externals ::  [External]
externals =
         [ external "fix-intro" (promoteDefR fixIntro :: RewriteH Core)
                [ "rewrite a recursive binding into a non-recursive binding using fix"
                ] .+ Introduce .+ Context
         , external "fix-computation" (promoteExprBiR fixComputationRule :: BiRewriteH Core)
                [ "Fixed-Point Computation Rule",
                  "fix t f  <==>  f (fix t f)"
                ]
         , external "rolling-rule" (promoteExprBiR rollingRule :: BiRewriteH Core)
                [ "Rolling Rule",
                  "fix tyA (\\ a -> f (g a))  <==>  f (fix tyB (\\ b -> g (f b))"
                ]
         -- , external "fix-spec" (promoteExprR fixSpecialization :: RewriteH Core)
         --        [ "specialize a fix with a given argument"] .+ Shallow
         ]

--------------------------------------------------------------------------------------------------

-- |  @f = e@   ==\>   @f = fix (\\ f -> e)@
fixIntro :: RewriteH CoreDef
fixIntro = prefixFailMsg "fix introduction failed: " $
           do Def f _ <- idR
              f' <- constT $ cloneVarH id f
              Def f <$> (mkFix =<< (defT mempty (extractR $ substR f $ varToCoreExpr f') (\ () e' -> Lam f' e')))

--------------------------------------------------------------------------------------------------

-- | @fix ty f@  \<==\>  @f (fix ty f)@
fixComputationRule :: BiRewriteH CoreExpr
fixComputationRule = bidirectional computationL computationR
  where
    computationL :: RewriteH CoreExpr
    computationL = prefixFailMsg "fix computation rule failed: " $
                   do (_,f) <- isFixExpr
                      fixf  <- idR
                      return (App f fixf)

    computationR :: RewriteH CoreExpr
    computationR = prefixFailMsg "fix computation rule failed: " $
                   do App f fixf <- idR
                      (_,f') <- isFixExpr <<< constant fixf
                      guardMsg (exprAlphaEq f f') "external function does not match internal expression"
                      return fixf


-- | @fix tyA (\\ a -> f (g a))@  \<==\>  @f (fix tyB (\\ b -> g (f b))@
rollingRule :: BiRewriteH CoreExpr
rollingRule = bidirectional rollingRuleL rollingRuleR
  where
    rollingRuleL :: RewriteH CoreExpr
    rollingRuleL = prefixFailMsg "rolling rule failed: " $
                   withPatFailMsg wrongFixBody $
                   do (tyA, Lam a (App f (App g (Var a')))) <- isFixExpr
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
                        do (tyB, Lam b (App g (App f' (Var b')))) <- isFixExpr <<< constant fx
                           guardMsg (b == b') wrongFixBody
                           guardMsg (exprAlphaEq f f') "external function does not match internal expression"
                           (tyA,tyB') <- funsWithInverseTypes g f
                           guardMsg (eqType tyB tyB') "Type mismatch: this shouldn't have happened, report this as a bug."
                           rollingRuleResult tyA f g

    rollingRuleResult :: Type -> CoreExpr -> CoreExpr -> TranslateH z CoreExpr
    rollingRuleResult ty f g = do x <- constT (newIdH "x" ty)
                                  mkFix (Lam x (App f (App g (Var x))))

    wrongFixBody :: String
    wrongFixBody = "body of fix does not have the form: Lam v (App f (App g (Var v)))"

--------------------------------------------------------------------------------------------------

-- ironically, this is an instance of worker/wrapper itself.

-- fixSpecialization :: RewriteH CoreExpr
-- fixSpecialization = do

--         -- fix (t::*) (f :: t -> t) (a :: t) :: t
--         App (App (App (Var fixId) (Type _)) _) _ <- idR

--         guardIsFixId fixId

--         let r :: RewriteH CoreExpr
--             r = multiEtaExpand [TH.mkName "f",TH.mkName "a"]

--             sub :: RewriteH Core
--             sub = pathR [0,1] (promoteR r)

--         App (App (App (Var fx) (Type t))
--                  (Lam _ (Lam v2 (App (App e _) _a2)))
--             )
--             (Type t2) <- extractR sub -- In normal form now

--         constT $ do let t' = applyTy t t2

--                     v3 <- newIdH "f" t'
--                     v4 <- newTyVarH "a" (tyVarKind v2)

--                     -- f' :: \/ a -> T [a] -> (\/ b . T [b])
--                     let f' = Lam v4 (Cast (Var v3) (mkUnsafeCo t' (applyTy t (mkTyVarTy v4))))
--                         e' = Lam v3 (App (App e f') (Type t2))

--                     return $ App (App (Var fx) (Type t')) e'


--------------------------------------------------------------------------------------------------

-- | Check that the expression has the form "fix t (f :: t -> t)", returning "t" and "f".
isFixExpr :: TranslateH CoreExpr (Type,CoreExpr)
isFixExpr = withPatFailMsg (wrongExprForm "fix t f") $ -- fix :: forall a. (a -> a) -> a
            do App (App (Var fixId) (Type ty)) f <- idR
               fixId' <- findFixId
               guardMsg (fixId == fixId') (var2String fixId ++ " does not match " ++ fixLocation)
               return (ty,f)

--------------------------------------------------------------------------------------------------

-- | f  ==>  fix f
mkFix :: CoreExpr -> TranslateH z CoreExpr
mkFix f = do t <- endoFunType f
             fixId <- findFixId
             return $ mkCoreApps (varToCoreExpr fixId) [Type t, f]

fixLocation :: String
fixLocation = "Data.Function.fix"

findFixId :: TranslateH a Id
findFixId = findIdT (TH.mkName fixLocation)

--------------------------------------------------------------------------------------------------
