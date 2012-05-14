{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins
import Data.List (nub)

import Control.Applicative

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.External

import Language.HERMIT.Primitive.Core
import Language.HERMIT.Primitive.Subst

import Language.HERMIT.HermitEnv as Env

import qualified Language.Haskell.TH as TH


promoteR'  :: Term a => RewriteH a -> RewriteH (Generic a)
promoteR' rr = rewrite $ \ c e ->  liftA inject (maybe (fail "argument is not an expr") (apply rr c)  (retract e))

externals :: [External]
externals =
         [
           external "eta-reduce" (promoteR eta_reduce)
                [ "(\\ v -> E1 v) ==> E1, fails otherwise" ]
         , external "eta-expand" (promoteR' . eta_expand)
                [ "'eta-expand v' performs E1 ==> (\\ v -> E1 v), fails otherwise" ]
         , external "let-intro" (promoteR' . let_intro)
                [ "'let-intro v' performs E1 ==> (let v = E1 in v)" ]
         , external "subst" (promoteR subst)
                [ "(let v = E1 in E2) ==> E2[E1/v], fails otherwise"
                , "condition: let is not-recursive" ]
         , external "dce" (promoteR dce)
                [ "dead code elimination removes a let. (let v = E1 in E2) ==> E2, if v is not free in E2,  fails otherwise"
                , "condition: let is not-recursive" ]
         , external "var" (\ nm -> promoteR . var nm . extractR)
                [ "'var <v>' applies a rewrite to all <v>" ]
         , external "info" (promoteT info)
                [ "tell me what you know about this expression or binding" ]
         , external "freevars" (promoteT freeVarsQuery)
                [ "List the free variables in this expression." ]
         , external "expr-type" (promoteT exprTypeQueryT)
                [ "List the type (Constructor) for this expression."]
         ]

eta_reduce :: RewriteH CoreExpr
eta_reduce = rewrite $ \ c e -> case e of
        Lam v1 (App f (Var v2)) | v1 == v2 -> do freesinFunction <- apply freeVarsT c f
                                                 if v1 `elem` freesinFunction
                                                  then fail $ "eta_reduce failed. " ++ showSDoc (ppr v1) ++
                                                              " is free in the function being applied."
                                                  else return f
        _ -> fail "eta_reduce failed"

eta_expand :: TH.Name -> RewriteH CoreExpr
eta_expand nm = rewrite $ \ _ e -> do
        -- First find the type of of e
        let ty = exprType e
        liftIO $ putStrLn $ showSDoc $ ppr ty
        case splitAppTy_maybe ty of
           Nothing -> fail "eta-expand failed (expression is not an App)"
           Just (_ , a_ty) -> do
             v1 <- newVarH nm a_ty
             liftIO $ putStr $ showSDoc $ ppr v1
             return $ Lam v1 (App e (Var v1))

let_intro ::  TH.Name -> RewriteH CoreExpr
let_intro nm = rewrite $ \ _ e -> do letvar <- newVarH nm (exprType e)
                                     return $ Let (NonRec letvar e) (Var letvar)

-- | 'subst' assumes that the input expression is of the form 'let v = E1 in E2'.
subst :: RewriteH CoreExpr
subst = rewrite $ \ c e -> case e of
        _ -> fail "subst failed (NOT implemented)"

-- dead code elimination removes a let.
-- (let v = E1 in E2) => E2, if v is not free in E2
dce :: RewriteH CoreExpr
dce = rewrite $ \ _ e -> case e of
        Let (NonRec n e1) e2 | n `notElem` freeIds e2 -> return e2
        -- Neil: Should there not be a case here for when n `elem` freeIds e2?
        _ -> fail "DCE failed. Not applied to a NonRec Let."

-- Others
-- let v = E1 in E2 E3 <=> (let v = E1 in E2) E3
-- let v = E1 in E2 E3 <=> E2 (let v = E1 in E3)

-- A few Queries.

-- info currently outputs the type of the current CoreExpr
info :: TranslateH CoreExpr String
info = liftT (("type ::= " ++) . showSDoc . ppr . exprType)

-- output a list of all free variables in the Expr.
freeVarsQuery :: TranslateH CoreExpr String
freeVarsQuery = (("FreeVars are: " ++) . show . map (showSDoc.ppr) . nub) <$> freeVarsT

freeVarsT :: TranslateH CoreExpr [Id]
freeVarsT = translate $ \ _ e -> apply (crushtdT $ tryT [] $ promoteT freeVarsExprT) initHermitEnv (inject e)

freeVarsExprT :: TranslateH CoreExpr [Id]
freeVarsExprT = translate $ \ c e -> return $ case e of
                                                Var n | Nothing <- lookupHermitBinding n c  -> [n]
                                                _                                           -> []

exprTypeQueryT :: TranslateH CoreExpr String
exprTypeQueryT = liftT $ \ e -> case e of
                                  Var _        -> "Var"
                                  Type _       -> "Type"
                                  Lit _        -> "Lit"
                                  App _ _      -> "App"
                                  Lam _ _      -> "Lam"
                                  Let _ _      -> "Let"
                                  Case _ _ _ _ -> "Case"
                                  Cast _ _     -> "Cast"
                                  Tick _ _     -> "Tick"
                                  Coercion _   -> "Coercion"

var :: TH.Name -> RewriteH CoreExpr -> RewriteH CoreExpr
var _ n = idR -- bottomupR (varR (\ n -> ()) ?
