-- Andre Santos' Local Transformations (Ch 3 in his dissertation)
module Language.HERMIT.Primitive.Local where

import GhcPlugins hiding (freeVars)

import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.External

import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Debug

import qualified Language.HERMIT.Primitive.Local.Case as Case
import qualified Language.HERMIT.Primitive.Local.Let as Let

import qualified Language.Haskell.TH as TH

import Control.Arrow

------------------------------------------------------------------------------

externals :: [External]
externals =
         [ external "beta-reduce" (promoteR beta_reduce :: RewriteH Core)
                     [ "((\\ v -> E1) E2) ==> let v = E2 in E1, fails otherwise"
                     , "this form of beta reduction is safe if E2 is an arbitrary"
                     , "expression (won't duplicate work)" ]                                 .+ Eval .+ Shallow
         , external "beta-reduce-plus" (promoteR betaReducePlus :: RewriteH Core)
                     [ "perform one or more beta-reductions"]                                .+ Eval .+ Shallow .+ Bash
         , external "beta-expand" (promoteR beta_expand :: RewriteH Core)
                     [ "(let v = E1 in E2) ==> (\\ v -> E2) E1, fails otherwise" ]           .+ Shallow
         , external "dead-code-elimination" (promoteR dce :: RewriteH Core)
                     [ "dead code elimination removes a let."
                     , "(let v = E1 in E2) ==> E2, if v is not free in E2, fails otherwise"
                     , "condition: let is not-recursive" ]                                   .+ Eval .+ Shallow .+ Bash
         , external "eta-reduce" (promoteR eta_reduce :: RewriteH Core)
                     [ "(\\ v -> E1 v) ==> E1, fails otherwise" ]                            .+ Eval .+ Shallow .+ Bash
         , external "eta-expand" (promoteR . eta_expand :: TH.Name -> RewriteH Core)
                     [ "'eta-expand v' performs E1 ==> (\\ v -> E1 v), fails otherwise" ]    .+ Shallow .+ Introduce
         ]
         ++ Let.externals
         ++ Case.externals

------------------------------------------------------------------------------

beta_reduce :: RewriteH CoreExpr
beta_reduce = setFailMsg "beta_reduce failed. Not applied to an App." $
    do App (Lam v e1) e2 <- idR
       return $ Let (NonRec v e2) e1


betaReducePlus :: RewriteH CoreExpr
betaReducePlus = do
        e <- idR
        let (f,xs) = collectArgs e
        guardMsg (length xs /= 0) "betaReducePlus, no applications"

        let (vs,e0) = collectBinders f

        guardMsg (length vs >= length xs) "betaReducePlus, no lambdas"

        let (vs1,vs2) = splitAt (length xs) vs

        (return
           $ mkLets (zipWith NonRec vs1 xs)
           $ mkLams vs2 e0) >>> observeR "beta-reduce-plus(final)"


{-

        tagFailR "betaReducePlus failed." $
        appT liftLambda idR App >>> beta_reduce
  where
          -- lift lambda finds the (perhaps hidden) lambda, and brings it out
          liftLambda = observeR "pre-liftLambda" >>> liftLambda' >>> observeR "post-liftLambda"
          liftLambda' =
                   (do e@(Lam {}) <- idR
                       return e)
                <+ (betaReducePlus
                        >>> observeR "liftLambda(UP)"
                            -- let v = e in ...
                            -- TODO: check scope here
                        >>> (do Let bds (Lam v e) <- idR
                                return (Lam v (Let bds e)))
                   )
-}

--betaReducePlus :: RewriteH CoreExpr
--betaReducePlus decent lift op = decent (tryR (betaReducePlus decent lift op >>> lift)) >>> op





     -- contextfreeT $ \ e -> case e of
     --    App (Lam v e1) e2 -> return $ Let (NonRec v e2) e1
     --    _ -> fail "beta_reduce failed. Not applied to an App."

beta_expand :: RewriteH CoreExpr
beta_expand = setFailMsg "beta_expand failed. Not applied to a NonRec Let." $
    do Let (NonRec v e2) e1 <- idR
       return $ App (Lam v e1) e2

  -- contextfreeT $ \ e -> case e of
  --       Let (NonRec v e2) e1 -> return $ App (Lam v e1) e2
  --       _ -> fail "beta_expand failed. Not applied to a NonRec Let."

------------------------------------------------------------------------------

eta_reduce :: RewriteH CoreExpr
eta_reduce = withPatFailMsg "eta_reduce failed. Not applied to Lam-App-Var" $
    do Lam v1 (App f (Var v2)) <- idR
       guardMsg (v1 == v2) "eta_reduce failed, variables are not equal."
       guardMsg (v1 `notElem` freeIds f) $ "eta_reduce failed. " ++ showSDoc (ppr v1) ++ "is free in the function being applied."
       return f

eta_expand :: TH.Name -> RewriteH CoreExpr
eta_expand nm = contextfreeT $ \ e -> case splitFunTy_maybe (exprType e) of
                                  Nothing          -> fail "eta-expand failed (expression is not an App)"
                                  Just (arg_ty, _) -> do v1 <- newVarH nm arg_ty
                                                         return $ Lam v1 (App e (Var v1))

------------------------------------------------------------------------------

-- dead code elimination removes a let.
-- (let v = E1 in E2) => E2, if v is not free in E2
dce :: RewriteH CoreExpr
dce = contextfreeT $ \ e -> case e of
        Let (NonRec n _) e2 | n `notElem` freeVars e2 -> return e2
                            | otherwise               -> fail "DCE: no dead code"
        _ -> fail "DCE: not applied to a NonRec Let."

------------------------------------------------------------------------------

-- NOT IN USE.  Use the GHC version instead.
{-
-- notice that we pass in the (empty) initial Hermit environment.
-- Notice the use of "mtryT".  This ensures all failures are converted to []s (the unit of the monoid).
freeVarsExpr :: CoreExpr -> HermitM [Id]
freeVarsExpr = fmap nub . apply (crushtdT $ promoteT freeVarT) initHermitEnv . ExprCore
  where
    freeVarT :: TranslateH CoreExpr [Id]
    freeVarT = do (c,Var n) <- exposeT
                  guard (not (n `boundInHermit` c))
                  return [n]
-}
------------------------------------------------------------------------------
