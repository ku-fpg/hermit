-- Andre Santos' Local Transformations (Ch 3 in his dissertation)
module Language.HERMIT.Primitive.Local where

import GhcPlugins

import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.External

import Language.HERMIT.Primitive.GHC
-- import Language.HERMIT.Primitive.Debug

import qualified Language.HERMIT.Primitive.Local.Case as Case
import qualified Language.HERMIT.Primitive.Local.Let as Let

import qualified Language.Haskell.TH as TH

import Control.Arrow

------------------------------------------------------------------------------

externals :: [External]
externals =
         [ external "beta-reduce" (promoteExprR beta_reduce :: RewriteH Core)
                     [ "((\\ v -> E1) E2) ==> let v = E2 in E1, fails otherwise"
                     , "this form of beta reduction is safe if E2 is an arbitrary"
                     , "expression (won't duplicate work)" ]                                 .+ Eval .+ Shallow
         , external "beta-reduce-plus" (promoteExprR betaReducePlus :: RewriteH Core)
                     [ "perform one or more beta-reductions"]                                .+ Eval .+ Shallow .+ Bash
         , external "beta-expand" (promoteExprR beta_expand :: RewriteH Core)
                     [ "(let v = E1 in E2) ==> (\\ v -> E2) E1, fails otherwise" ]           .+ Shallow
         , external "dead-code-elimination" (promoteExprR dce :: RewriteH Core)
                     [ "dead code elimination removes a let."
                     , "(let v = E1 in E2) ==> E2, if v is not free in E2, fails otherwise"
                     , "condition: let is not-recursive" ]                                   .+ Eval .+ Shallow .+ Bash
         , external "eta-reduce" (promoteExprR eta_reduce :: RewriteH Core)
                     [ "(\\ v -> E1 v) ==> E1, fails otherwise" ]                            .+ Eval .+ Shallow .+ Bash
         , external "eta-expand" (promoteExprR . eta_expand :: TH.Name -> RewriteH Core)
                     [ "'eta-expand v' performs E1 ==> (\\ v -> E1 v), fails otherwise" ]    .+ Shallow .+ Introduce
         ]
         ++ Let.externals
         ++ Case.externals

------------------------------------------------------------------------------

beta_reduce :: RewriteH CoreExpr
beta_reduce = setFailMsg "beta_reduce failed. Not applied to an App." $
    do App (Lam v e1) e2 <- idR
       return $ Let (NonRec v e2) e1


multiBetaReduce :: (Int -> Bool) -> RewriteH CoreExpr
multiBetaReduce p = do
        e <- idR
        let (f,xs) = collectArgs e
        guardMsg (p (length xs)) "multiBetaReduce, incorrect number of arguments"

        let (vs,e0) = collectBinders f

        guardMsg (length vs >= length xs) "multiBetaReduce, insufficent lambdas"

        let (vs1,vs2) = splitAt (length xs) vs

        return
           $ mkLets (zipWith NonRec vs1 xs)
           $ mkLams vs2 e0

-- TODO: inline this everywhere
betaReducePlus :: RewriteH CoreExpr
betaReducePlus = multiBetaReduce (> 0)

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


beta_expand :: RewriteH CoreExpr
beta_expand = setFailMsg "beta_expand failed. Not applied to a NonRec Let." $
    do Let (NonRec v e2) e1 <- idR
       return $ App (Lam v e1) e2

------------------------------------------------------------------------------

eta_reduce :: RewriteH CoreExpr
eta_reduce = withPatFailMsg "eta_reduce failed. Not applied to Lam-App-Var" $
   (do Lam v1 (App f (Var v2)) <- idR
       guardMsg (v1 == v2) "eta_reduce failed, variables are not equal."
       guardMsg (v1 `notElem` coreExprFreeIds f) $ "eta_reduce failed. " ++ showSDoc (ppr v1) ++ "is free in the function being applied."
       return f) <+
   (do Lam v1 (App f (Type ty)) <- idR
       Just v2 <- return (getTyVar_maybe ty)
       guardMsg (v1 == v2) "eta_reduce failed, type variables are not equal."
       guardMsg (v1 `notElem` coreExprFreeVars f) $ "eta_reduce failed. " ++ showSDoc (ppr v1) ++ "is free in the function being applied."
       return f)

eta_expand :: TH.Name -> RewriteH CoreExpr
eta_expand nm = contextfreeT $ \ e ->
        case splitFunTy_maybe (exprType e) of
          Just (arg_ty, _) -> do v1 <- newVarH nm arg_ty
                                 return $ Lam v1 (App e (Var v1))
          _ -> case splitForAllTy_maybe (exprType e) of
                  Just (v,_) -> do v1 <- newTypeVarH nm (tyVarKind v)
                                   return $ Lam v1 (App e (Type (mkTyVarTy v1)))
                  Nothing -> fail "eta-expand failed"

multiEtaExpand :: [TH.Name] -> RewriteH CoreExpr
multiEtaExpand []       = idR
multiEtaExpand (nm:nms) = eta_expand nm >>> lamR (multiEtaExpand nms)

------------------------------------------------------------------------------

-- dead code elimination removes a let.
-- (let v = E1 in E2) => E2, if v is not free in E2
dce :: RewriteH CoreExpr
dce = withPatFailMsg "dce failed.  Not applied to a NonRec-Let." $
      do Let (NonRec v _) e <- idR
         guardMsg (v `notElem` coreExprFreeVars e) "dce failed.  No dead code to eliminate."
         return e

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
