-- Andre Santos' Local Transformations (Ch 3 in his dissertation)
module Language.HERMIT.Primitive.Local where

import GhcPlugins

import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.External

import Language.HERMIT.Primitive.GHC
-- import Language.HERMIT.Primitive.Debug

import Language.HERMIT.Primitive.Common
import qualified Language.HERMIT.Primitive.Local.Case as Case
import qualified Language.HERMIT.Primitive.Local.Let as Let

import qualified Language.Haskell.TH as TH

import Control.Arrow

------------------------------------------------------------------------------

externals :: [External]
externals =
         [ external "beta-reduce" (promoteExprR betaReduce :: RewriteH Core)
                     [ "((\\ v -> E1) E2) ==> let v = E2 in E1, fails otherwise"
                     , "this form of beta reduction is safe if E2 is an arbitrary"
                     , "expression (won't duplicate work)" ]                                 .+ Eval .+ Shallow
         , external "beta-reduce-plus" (promoteExprR betaReducePlus :: RewriteH Core)
                     [ "perform one or more beta-reductions"]                                .+ Eval .+ Shallow .+ Bash
         , external "beta-expand" (promoteExprR betaExpand :: RewriteH Core)
                     [ "(let v = E1 in E2) ==> (\\ v -> E2) E1, fails otherwise" ]           .+ Shallow
         , external "dead-code-elimination" (promoteExprR dce :: RewriteH Core)
                     [ "dead code elimination removes a let."
                     , "(let v = E1 in E2) ==> E2, if v is not free in E2, fails otherwise"
                     , "condition: let is not-recursive" ]                                   .+ Eval .+ Shallow .+ Bash
         , external "eta-reduce" (promoteExprR etaReduce :: RewriteH Core)
                     [ "(\\ v -> E1 v) ==> E1, fails otherwise" ]                            .+ Eval .+ Shallow .+ Bash
         , external "eta-expand" (promoteExprR . etaExpand :: TH.Name -> RewriteH Core)
                     [ "'eta-expand v' performs E1 ==> (\\ v -> E1 v), fails otherwise" ]    .+ Shallow .+ Introduce
         ]
         ++ Let.externals
         ++ Case.externals

------------------------------------------------------------------------------

betaReduce :: RewriteH CoreExpr
betaReduce = prefixFailMsg "Beta reduction failed: " $
             setFailMsg (wrongExprForm "App (Lam v e1) e2") $
    do App (Lam v e1) e2 <- idR
       return $ Let (NonRec v e2) e1

multiBetaReduce :: (Int -> Bool) -> RewriteH CoreExpr
multiBetaReduce p = prefixFailMsg "Multi-Beta-Reduce failed: " $
    do
        e <- idR
        let (f,xs) = collectArgs e
        guardMsg (p (length xs)) "incorrect number of arguments."

        let (vs,e0) = collectBinders f

        guardMsg (length vs >= length xs) "insufficent lambdas."

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

betaExpand :: RewriteH CoreExpr
betaExpand = setFailMsg ("Beta expansion failed: " ++ wrongExprForm "Let (NonRec v e1) e2") $
    do Let (NonRec v e2) e1 <- idR
       return $ App (Lam v e1) e2

------------------------------------------------------------------------------

etaReduce :: RewriteH CoreExpr
etaReduce = do
    dynFlags <- constT getDynFlags
    prefixFailMsg "Eta reduction failed: " $
      withPatFailMsg (wrongExprForm "Lam v1 (App f (Var v2))") $
       (do Lam v1 (App f (Var v2)) <- idR
           guardMsg (v1 == v2) "the expression has the right form, but the variables are not equal."
           guardMsg (v1 `notElem` coreExprFreeIds f) $ showPpr dynFlags v1 ++ " is free in the function being applied."
           return f) <+
       (do Lam v1 (App f (Type ty)) <- idR
           Just v2 <- return (getTyVar_maybe ty)
           guardMsg (v1 == v2) "type variables are not equal."
           guardMsg (v1 `notElem` coreExprFreeVars f) $ showPpr dynFlags v1 ++ " is free in the function being applied."
           return f)

etaExpand :: TH.Name -> RewriteH CoreExpr
etaExpand nm = prefixFailMsg "Eta expansion failed: " $
               contextfreeT $ \ e ->
        case splitFunTy_maybe (exprType e) of
          Just (arg_ty, _) -> do v1 <- newVarH (show nm) arg_ty
                                 return $ Lam v1 (App e (Var v1))
          _ -> case splitForAllTy_maybe (exprType e) of
                  Just (v,_) -> do v1 <- newTypeVarH (show nm) (tyVarKind v)
                                   return $ Lam v1 (App e (Type (mkTyVarTy v1)))
                  Nothing -> fail "TODO: Add useful error message here."

multiEtaExpand :: [TH.Name] -> RewriteH CoreExpr
multiEtaExpand []       = idR
multiEtaExpand (nm:nms) = etaExpand nm >>> lamR (multiEtaExpand nms)

------------------------------------------------------------------------------

-- dead code elimination removes a let.
-- (let v = E1 in E2) => E2, if v is not free in E2
dce :: RewriteH CoreExpr
dce = prefixFailMsg "Dead code elimination failed: " $
      withPatFailMsg (wrongExprForm "Let (NonRec v e1) e2") $
      do Let (NonRec v _) e <- idR
         guardMsg (v `notElem` coreExprFreeVars e) "Dead code elimination failed.  No dead code to eliminate."
         return e

------------------------------------------------------------------------------
