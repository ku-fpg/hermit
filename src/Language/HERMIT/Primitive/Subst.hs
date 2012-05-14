{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

module Language.HERMIT.Primitive.Subst where

import GhcPlugins hiding ((<>))
import qualified Data.Map as Map
import qualified Data.List as List

import Language.KURE
import Control.Applicative

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv as Env
import Language.HERMIT.External
import Language.HERMIT.Primitive.Core

import qualified Language.Haskell.TH as TH



externals :: [External]
externals =
         [
           external "alpha" (promoteR alphaLambda)
                [ "Alpha rename (for Lambda's)."]
         , external "let-sub" (promoteR letSubstR)
                [ "Let substitution."]
         ]

bindList :: Bind Id -> [Id]
bindList (NonRec b _) = [b]

bindList (Rec binds) = map fst binds

-- The alpha renaming functions defined here,
-- rely on a function to return a globally fresh Id,
-- therefore, they do not require a list of Id's which must not clash.
alphaLambda :: RewriteH CoreExpr
alphaLambda = rewrite $ \ c exp ->
          case exp of
            (Lam b e) ->
                let bNamestring = TH.mkName $ showSDoc (ppr b)
                in
                  case splitFunTy_maybe (exprType exp) of
                    -- Not the best error message provided here.
                    -- Is this really (all) that can be happening here?
                    Nothing -> fail "Cannot rename. Lambda argument is a TyVar."
                    Just (domain_ty, arg_ty) -> do
                      freshId <-newVarH bNamestring domain_ty
                      Lam freshId <$> apply (substR b (Var freshId)) (c @@ 0) e
            _ -> fail "expr is not a Lambda"

-- Replace each var bound in a let expr with a globally fresh Id.
alphaLet = rewrite $ \ c exp ->
        case exp of
            (Let (NonRec b be) e) ->
                let bNamestring = TH.mkName $ showSDoc (ppr b)
                in
                  case splitFunTy_maybe (exprType exp) of
                    Nothing -> fail "Cannot rename. Lambda argument is a TyVar."
                    Just (domain_ty, arg_ty) -> do
                      freshId <-newVarH bNamestring domain_ty
                      Lam freshId <$> apply (substR b (Var freshId)) (c @@ 0) e
            (Let (Rec binds) e) -> fail "Have not yet implemented alpha renaming for recursive let"
            _ -> fail "expr is not a Lambda"

letSubstR :: RewriteH CoreExpr
letSubstR = rewrite $ \ c exp ->
    case exp of
      (Let (NonRec b be) e) -> do  apply (substR b be) c e
      _ -> fail "LetSubst failed. Expr is not a Non-recursive Let."

-- Andy's substitution rewrite
--  E [ v::r ] ===   let (NonRec v = r) in E
--      and then inline "v"


-- | Substitution

substRG :: Id -> CoreExpr  -> RewriteH Core
substRG v e = promoteR $ substR v e

substR :: Id -> CoreExpr  -> RewriteH CoreExpr
substR v expReplacement = (rule12 <+ rule345 <+ rule78 {- <+ rule9 -} )  <+ rule6
    where -- The 6 rules from the textbook for the simple lambda calculus.
        rule12 :: RewriteH CoreExpr
        rule12 = rewrite $ \ c exp ->
                 case exp of
                   Var n0 | (n0 == v)  -> return expReplacement
                   Var n0  -> return exp
                   _ -> fail $ "Not a matching Var"
        rule345 :: RewriteH CoreExpr
        rule345 = rewrite $ \ c exp ->
                  case exp of
                    Lam b e | (b == v) -> return exp
                    Lam b e | (b `notElem` freeIds expReplacement) ->
                                Lam b <$> apply (allR (substRG v expReplacement))  (c @@ 0) e
                    Lam b e | (v `notElem` freeIds e) -> return exp
                    Lam b e ->
                        Lam b <$> apply (alphaLambda  >-> substR v expReplacement) (c @@ 0) e
                    _ -> fail $ "not a Lambda"

        rule6 = allR (substRG v expReplacement)
        -- like Rule 3 and 4/5 above, but for lets
        rule78 :: RewriteH CoreExpr
        rule78 = rewrite $ \ c exp ->
                 case exp of
                   Let bds e | (v `elem` (bindList bds)) -> return exp
                   -- Don't we need to perform the subst over the let-bound expr's ???
                   -- edk It appears that we need to effectively replicate code from allR for Let here ???
                   Let bds e | (null $ List.intersect (bindList bds) (freeIds expReplacement)) ->
                                 Let <$> apply (allR (substRG v expReplacement)) (c @@ 0) bds
                                         <*>  apply (allR (substRG v expReplacement)) (c @@ 1) e
                   -- If v is not free in e, it may be free in the expression(s) bound by the let
                   Let bds e | (v `notElem` freeIds e) ->
                                 do bds' <- apply (allR (substRG v expReplacement)) (c @@ 0) bds
                                    return (Let bds' e)
                   -- final case.  v is free in e, but the bound var(s) in the let appear
                   -- edk free in the replacement expression.  Alpha renaming to the rescue, and try again.
                   Let _ _ -> apply (alphaLet  >-> (substR v expReplacement)) c exp
                   _ -> fail $ "not a Let"

        rule9 = subst4Case v expReplacement

-- cases are a bit different, since v may be free in some branches but not in others
subst4Case :: Id -> CoreExpr -> RewriteH CoreExpr
subst4Case v expReplacement = rewrite $ \ c exp ->
          case exp of
            (Case e b ty alts) -> do
                     e' <- apply (substR v expReplacement) (c @@ 0) e
                     -- edk.  If 'b' is free in expReplacement, there is more work to do
                     alts' <- sequence [apply (subst4Alt v expReplacement) (c @@ n) alt
                                           | (alt,n) <- zip alts [1..] ]
                     return $ Case e' b ty alts'

subst4Alt :: Id -> CoreExpr -> RewriteH CoreAlt
subst4Alt v expReplacement = undefined
