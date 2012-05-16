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
         , external "alpha-let" (promoteR alphaNonRecLet)
                [ "Alpha rename (for Let)."]
         , external "let-sub" (promoteR letSubstR)
                [ "Let substitution."]
         ]

bindList :: Bind Id -> [Id]
bindList (NonRec b _) = [b]

bindList (Rec binds) = map fst binds


lamVar :: TranslateH CoreExpr Id
lamVar = lamT (pure ()) const

letNonRecVarAndType :: TranslateH CoreExpr (Id,Type)
letNonRecVarAndType = letNonRecT idR (pure ()) (\ v e1 _ -> (v,exprType e1))

letCaseVarAndType :: TranslateH CoreExpr (Id, Type)
letCaseVarAndType = caseT idR (\ _ -> idR) (\ _ v ty _ -> (v, ty))

-- returns (DomainType,ArgType)
lamTypes :: TranslateH CoreExpr (Type,Type)
lamTypes = liftMT (maybe (fail "Lambda argument is a TyVar.") pure . splitFunTy_maybe . exprType)
                                         -- Not the best error message provided here.
                                         -- Is this really (all) that can be happening here?

varNameH :: Id -> TH.Name
varNameH = TH.mkName . showSDoc . ppr

-- The alpha renaming functions defined here,
-- rely on a function to return a globally fresh Id,
-- therefore, they do not require a list of Id's which must not clash.
alphaLambda :: RewriteH CoreExpr
alphaLambda = do v <- lamVar
                 (dom_ty, _) <- lamTypes
                 v' <- constMT $ newVarH (varNameH v) dom_ty
                 lamT (substR v $ Var v') (\ _ -> Lam v')


-- Replace each var bound in a let expr with a globally fresh Id.

alphaNonRecLet :: RewriteH CoreExpr
alphaNonRecLet = do (v,ty) <- letNonRecVarAndType
                    v' <- constMT $ newVarH (varNameH v) ty
                    letNonRecT idR (substR v $ Var v') (\ _ e1 e2 -> Let (NonRec v' e1) e2)

alphaRecLet :: RewriteH CoreExpr
alphaRecLet = fail "Unable to perform alpha renaming for recursiveLet."

alphaLet :: RewriteH CoreExpr
alphaLet = alphaNonRecLet >-> alphaRecLet

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
substR v expReplacement = (rule12 <+ rule345 <+ rule78 <+ rule9)  <+ rule6
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
                                apply (lamT (substR v expReplacement) Lam) c exp
                    Lam b e | (v `notElem` freeIds e) -> return exp
                    Lam b e ->
                        apply (alphaLambda  >-> lamT (substR v expReplacement) Lam) c exp
                    _ -> fail $ "not a Lambda"

        rule6 = allR (substRG v expReplacement)
        -- like Rule 3 and 4/5 above, but for lets
        rule78 :: RewriteH CoreExpr
        rule78 = rewrite $ \ c exp ->
                 case exp of
                   Let bds e | (v `elem` (bindList bds)) -> return exp
                   Let bds e | (null $ List.intersect (bindList bds) (freeIds expReplacement)) ->
                                 apply (letT (substBindR v expReplacement)  (substR v expReplacement)  Let) c exp
                   -- If v is not free in e, it may be free in the expression(s) bound by the let
                   Let bds e | (v `notElem` freeIds e) ->
                                 apply (letT (substBindR v expReplacement) idR Let) c exp
                   -- final case.  v is free in e, but the bound var(s) in the let appear
                   -- free in the replacement expression.  Alpha renaming to the rescue, and try again.
                   Let _ _ -> apply (alphaLet  >-> (letT idR (substR v expReplacement) Let)) c exp
                   _ -> fail $ "not a Let"
        -- edk?  Do we need to worry about clashes with the VBind component of a Case?
        --  For now, it is ignored here.
        rule9 = caseT (substR v expReplacement) (\_ -> substAltR v expReplacement) Case


substAltR :: Id -> CoreExpr -> RewriteH CoreAlt
substAltR v expReplacement = rewrite $ \ c exp ->
      case exp of
        (con, bs, e) | v `elem` bs -> return exp
                     | (null $ List.intersect bs (freeIds expReplacement)) ->
                         apply (altT (substR v expReplacement)  (,,)) c exp
                     | otherwise -> fail "Do not handle clashes with Case bound variables yet."


substBindR :: Id -> CoreExpr  -> RewriteH CoreBind
substBindR v expReplacement = rewrite $ \ c exp ->
       case exp of
         (NonRec b e) | b == v -> return exp
                      | (b `notElem` freeIds expReplacement) -> apply (nonRecT (substR v expReplacement) NonRec) c exp
                      | otherwise -> return exp
         _ -> fail "Do not handle recursive lets yet."
