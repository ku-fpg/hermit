module Language.HERMIT.Primitive.Local
       ( -- * Local Structural Manipulations
         Language.HERMIT.Primitive.Local.externals
         -- ** Let Expressions
       , module Language.HERMIT.Primitive.Local.Let
         -- ** Case Expressions
       , module Language.HERMIT.Primitive.Local.Case
         -- ** Miscellaneous
       , betaReduce
       , betaReducePlus
       , betaExpand
       , deadCodeElimination
       , etaReduce
       , etaExpand
       , multiEtaExpand
       , flattenModule
       , flattenProgram
       )
where

import GhcPlugins

import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.External
import Language.HERMIT.GHC

import Language.HERMIT.Primitive.GHC
-- import Language.HERMIT.Primitive.Debug

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Local.Case
import Language.HERMIT.Primitive.Local.Let

import qualified Language.Haskell.TH as TH

import Data.List(nub)

import Control.Arrow

------------------------------------------------------------------------------

-- | Externals for local structural manipulations.
--   (Many taken from Chapter 3 of Andre Santos' dissertation.)
externals :: [External]
externals =
         [ external "beta-reduce" (promoteExprR betaReduce :: RewriteH Core)
                     [ "((\\ v -> E1) E2) ==> let v = E2 in E1"
                     , "this form of beta-reduction is safe if E2 is an arbitrary"
                     , "expression (won't duplicate work)" ]                                 .+ Eval .+ Shallow
         , external "beta-reduce-plus" (promoteExprR betaReducePlus :: RewriteH Core)
                     [ "perform one or more beta-reductions."]                               .+ Eval .+ Shallow .+ Bash
         , external "beta-expand" (promoteExprR betaExpand :: RewriteH Core)
                     [ "(let v = e1 in e2) ==> (\\ v -> e2) e1" ]                            .+ Shallow
         , external "dead-code-elimination" (promoteExprR deadCodeElimination :: RewriteH Core)
                     [ "dead-code-elimination removes a let."
                     , "(let v = e1 in e2) ==> e2, if v is not free in e2."
                     , "condition: let is not-recursive" ]                                   .+ Eval .+ Shallow .+ Bash
         , external "eta-reduce" (promoteExprR etaReduce :: RewriteH Core)
                     [ "(\\ v -> e1 v) ==> e1" ]                                             .+ Eval .+ Shallow .+ Bash
         , external "eta-expand" (promoteExprR . etaExpand :: TH.Name -> RewriteH Core)
                     [ "\"eta-expand 'v\" performs e1 ==> (\\ v -> e1 v)" ]                     .+ Shallow .+ Introduce
         ]
         ++
         [ external "flatten-module" (promoteModGutsR flattenModule :: RewriteH Core)
                ["Flatten all the top-level binding groups in the module to a single recursive binding group.",
                 "This can be useful if you intend to appply GHC RULES."]
         , external "flatten-program" (promoteProgR flattenProgram :: RewriteH Core)
                ["Flatten all the top-level binding groups in a program (list of binding groups) to a single recursive binding group.",
                 "This can be useful if you intend to appply GHC RULES."]
         ]
         ++ letExternals
         ++ caseExternals

------------------------------------------------------------------------------

-- | ((\\ v -> e1) e2) ==> (let v = e2 in e1)
--   This form of beta-reduction is safe if e2 is an arbitrary
--   expression (won't duplicate work).
betaReduce :: RewriteH CoreExpr
betaReduce = setFailMsg ("Beta-reduction failed: " ++ wrongExprForm "App (Lam v e1) e2") $
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
-- Neil: Are we sure we want to inline this?
-- | Perform one or more beta-reductions.
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

-- | (let v = e1 in e2) ==> (\\ v -> e2) e1
betaExpand :: RewriteH CoreExpr
betaExpand = setFailMsg ("Beta-expansion failed: " ++ wrongExprForm "Let (NonRec v e1) e2") $
    do Let (NonRec v e1) e2 <- idR
       return $ App (Lam v e2) e1

------------------------------------------------------------------------------

-- | (\\ v -> e1 v) ==> e1
etaReduce :: RewriteH CoreExpr
etaReduce = prefixFailMsg "Eta-reduction failed: " $
            withPatFailMsg (wrongExprForm "Lam v1 (App f (Var v2))") $
       (do Lam v1 (App f (Var v2)) <- idR
           guardMsg (v1 == v2) "the expression has the right form, but the variables are not equal."
           guardMsg (v1 `notElem` coreExprFreeIds f) $ var2String v1 ++ " is free in the function being applied."
           return f) <+
       (do Lam v1 (App f (Type ty)) <- idR
           Just v2 <- return (getTyVar_maybe ty)
           guardMsg (v1 == v2) "type variables are not equal."
           guardMsg (v1 `notElem` coreExprFreeVars f) $ var2String v1 ++ " is free in the function being applied."
           return f)

-- | e1 ==> (\\ v -> e1 v)
etaExpand :: TH.Name -> RewriteH CoreExpr
etaExpand nm = prefixFailMsg "Eta-expansion failed: " $
               contextfreeT $ \ e ->
        case splitFunTy_maybe (exprType e) of
          Just (arg_ty, _) -> do v1 <- newVarH (show nm) arg_ty
                                 return $ Lam v1 (App e (Var v1))
          _ -> case splitForAllTy_maybe (exprType e) of
                  Just (v,_) -> do v1 <- newTypeVarH (show nm) (tyVarKind v)
                                   return $ Lam v1 (App e (Type (mkTyVarTy v1)))
                  Nothing -> fail "TODO: Add useful error message here."

-- | Perform multiple eta-expansions.
multiEtaExpand :: [TH.Name] -> RewriteH CoreExpr
multiEtaExpand []       = idR
multiEtaExpand (nm:nms) = etaExpand nm >>> lamR (multiEtaExpand nms)

------------------------------------------------------------------------------

-- | Dead-code-elimination removes a let.
--   (let v = E1 in E2) => E2, if v is not free in E2
deadCodeElimination :: RewriteH CoreExpr
deadCodeElimination = prefixFailMsg "Dead-code-elimination failed: " $
                      withPatFailMsg (wrongExprForm "Let (NonRec v e1) e2") $
      do Let (NonRec v _) e <- idR
         guardMsg (v `notElem` coreExprFreeVars e) "no dead code to eliminate."
         return e

------------------------------------------------------------------------------

-- | Flatten all the top-level binding groups in the module to a single recursive binding group.
flattenModule :: RewriteH ModGuts
flattenModule = modGutsR flattenProgram

-- | Flatten all the top-level binding groups in a program to a single recursive binding group.
flattenProgram :: RewriteH CoreProg
flattenProgram = contextfreeT $ \ p ->
                 let allbinds = foldr listOfBinds [] (progToBinds p)
                     nodups   = nub $ map fst allbinds
                 in
                    if length allbinds == length nodups
                     then return $ bindsToProg [Rec allbinds]
                     else fail "Top-level bindings contain multiple occurances of a name."
  where
        listOfBinds :: CoreBind -> [(Id,CoreExpr)] -> [(Id,CoreExpr)]
        listOfBinds (NonRec b e) others = (b, e) : others
        listOfBinds (Rec bds)    others = bds ++ others

------------------------------------------------------------------------------
