{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins

import Control.Applicative
import Control.Arrow

import Language.KURE
import Language.KURE.Injection

import Language.HERMIT.HermitMonad
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitKure
import Language.HERMIT.External
import Language.HERMIT.GHC

import qualified Language.Haskell.TH as TH


promoteR'  :: Term a => RewriteH a -> RewriteH (Generic a)
promoteR' rr = rewrite $ \ c e ->  inject <$> maybe (fail "argument is not an expr") (apply rr c)  (retract e)

externals :: [External]
externals = map (.+ Experiment)
         [
           external "let-intro" (promoteR' . let_intro :: TH.Name -> RewriteH Core)
                [ "'let-intro v' performs E1 ==> (let v = E1 in v)" ]
         , external "var" (\ nm -> promoteR . var nm . extractR :: RewriteH Core -> RewriteH Core)
                [ "'var <v>' applies a rewrite to all <v>" ] .+ Unimplemented
         , external "info" (promoteT info :: TranslateH Core String)
                [ "tell me what you know about this expression or binding" ] .+ Unimplemented
         , external "expr-type" (promoteT exprTypeQueryT :: TranslateH Core String)
                [ "List the type (Constructor) for this expression."]
         , external "test" (testQuery :: RewriteH Core -> TranslateH Core String)
                [ "determines if a rewrite could be successfully applied" ]
         ]

let_intro ::  TH.Name -> RewriteH CoreExpr
let_intro nm = rewrite $ \ _ e -> do letvar <- newVarH nm (exprType e)
                                     return $ Let (NonRec letvar e) (Var letvar)

-- Others
-- let v = E1 in E2 E3 <=> (let v = E1 in E2) E3
-- let v = E1 in E2 E3 <=> E2 (let v = E1 in E3)

-- A few Queries.

-- info currently outputs the type of the current CoreExpr
-- TODO: we need something for bindings, etc.
info :: TranslateH CoreExpr String
info = do ContextPath this <- pathT
          translate $ \ cxt e -> do
                  let hd = "Core Expr"
                      ty = "type ::= " ++ showSDoc (ppr (exprType e))
                      pa = "path :=  " ++ show (reverse this)
                      extra = "extra := " ++ case e of
                                Var v -> showSDoc (ppIdInfo v (idInfo v))
                                _ -> "{}"
                  return (unlines [hd,ty,pa,extra])


exprTypeQueryT :: TranslateH CoreExpr String
exprTypeQueryT = arr $ \ e -> case e of
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

testQuery :: RewriteH Core -> TranslateH Core String
testQuery r = f <$> testM r
  where
    f True  = "Rewrite would succeed."
    f False = "Rewrite would fail."

var :: TH.Name -> RewriteH CoreExpr -> RewriteH CoreExpr
var _ n = idR -- bottomupR (varR (\ n -> ()) ?

