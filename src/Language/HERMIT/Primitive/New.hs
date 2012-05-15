{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins

import Control.Applicative

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.External

import Language.HERMIT.Primitive.Core

import qualified Language.Haskell.TH as TH


promoteR'  :: Term a => RewriteH a -> RewriteH (Generic a)
promoteR' rr = rewrite $ \ c e ->  liftA inject (maybe (fail "argument is not an expr") (apply rr c)  (retract e))

externals :: [External]
externals =
         [
           external "let-intro" (promoteR' . let_intro)
                [ "'let-intro v' performs E1 ==> (let v = E1 in v)" ]
         , external "dce" (promoteR dce)
                [ "dead code elimination removes a let. (let v = E1 in E2) ==> E2, if v is not free in E2,  fails otherwise"
                , "condition: let is not-recursive" ]
         , external "var" (\ nm -> promoteR . var nm . extractR)
                [ "'var <v>' applies a rewrite to all <v>" ]
         , external "info" (promoteT info)
                [ "tell me what you know about this expression or binding" ]
         , external "expr-type" (promoteT exprTypeQueryT)
                [ "List the type (Constructor) for this expression."]
         ]

let_intro ::  TH.Name -> RewriteH CoreExpr
let_intro nm = rewrite $ \ _ e -> do letvar <- newVarH nm (exprType e)
                                     return $ Let (NonRec letvar e) (Var letvar)

-- dead code elimination removes a let.
-- (let v = E1 in E2) => E2, if v is not free in E2
dce :: RewriteH CoreExpr
dce = liftMT $ \ e -> case e of
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
