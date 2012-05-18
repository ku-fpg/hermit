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
         , external "alpha-alt" (promoteR alphaAlt)
                [ "Alpha rename (for a single Case Alternative)."]
         , external "alpha-case" (promoteR alphaCase)
                [ "Alpha renaming for each alternative of a Case.."]
         , external "let-sub" (promoteR letSubstR)
                [ "Let substitution."]
         ]

bindList :: Bind Id -> [Id]
bindList (NonRec b _) = [b]

bindList (Rec binds) = map fst binds


varNameH :: Id -> TH.Name
varNameH = TH.mkName . showSDoc . ppr

-- The alpha renaming functions defined here,
-- rely on a function to return a globally fresh Id,
-- therefore, they do not require a list of Id's which must not clash.
alphaLambda :: RewriteH CoreExpr
alphaLambda = do (Lam b e) <- idR
                 b' <- constMT $ newVarH (varNameH b) (idType b)
                 lamT (substR b $ Var b') (\ _ -> Lam b')


-- Replace each var bound in a let expr with a globally fresh Id.
alphaNonRecLet :: RewriteH CoreExpr
alphaNonRecLet = do Let (NonRec v e1) e2 <- idR
                    v' <- constMT $ newVarH (varNameH v) (exprType e1)
                    letNonRecT idR (substR v $ Var v') (\ _ e1 e2 -> Let (NonRec v' e1) e2)

alphaRecLet :: RewriteH CoreExpr
alphaRecLet = do (Let (Rec bds) e) <- idR
                 let boundIds = map fst bds
                 freshBoundIds <- sequence $ fmap (\ b -> constMT $ newVarH (varNameH b) (idType b)) boundIds
                 letRecT (\ _ -> (foldr seqSubst idR (zip boundIds freshBoundIds)))
                            (foldr seqSubst idR (zip boundIds freshBoundIds))
                            (\ bds' e' -> (Let (Rec bds') e'))
    where seqSubst (v,v') t = t >-> (substR v $ Var v')

alphaLet :: RewriteH CoreExpr
alphaLet = alphaNonRecLet <+ alphaRecLet

-- there is no alphaCase.
-- instead alphaAlt performs renaming over an individual Case alternative
alphaAlt :: RewriteH CoreAlt
alphaAlt = do (con, vs, e) <- idR
              freshBoundIds <- sequence $ fmap (\ v' -> constMT $ newVarH (varNameH v') (idType v')) vs
              altT (foldr seqSubst idR (zip vs freshBoundIds)) (\ _ _ e' -> (con, freshBoundIds, e'))
    where seqSubst (v,v') t = t >-> (substR v $ Var v')

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
        rule12 = do exp@(Var n0) <- idR
                    if (n0 == v)
                    then return expReplacement
                    else return exp

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

-- edk !! Note, this subst handles name clashes with variables bound in the Alt form,
-- since the scope of these bound variables is within the Alt.
substAltR :: Id -> CoreExpr -> RewriteH CoreAlt
substAltR v expReplacement =
    do (con, bs, e) <- idR
       case (v `elem` bs) of
         True -> return (con, bs, e)
         _ ->  case (null $ List.intersect bs (freeIds expReplacement)) of
                True -> altT (substR v expReplacement)  (,,)
                _    -> alphaAlt >-> (altT (substR v expReplacement)  (,,))


-- edk !! Note, this subst DOES NOT handles name clashes with variables bound in the Bind form,
-- since the scope of these bound variables extends beyond the form.
substBindR :: Id -> CoreExpr  -> RewriteH CoreBind
substBindR v expReplacement = (substNonRecBindR v expReplacement) <+ (substRecBindR v expReplacement)

substNonRecBindR :: Id -> CoreExpr  -> RewriteH CoreBind
substNonRecBindR v expReplacement =
    do exp@(NonRec b e) <- idR
       case (b == v) of
         True -> return exp
         _    -> case (b `notElem` freeIds expReplacement) of
                  True -> nonRecT (substR v expReplacement) NonRec
                  _    -> return exp

substRecBindR :: Id -> CoreExpr  -> RewriteH CoreBind
substRecBindR v expReplacement =
    do exp@(Rec bds) <- idR
       let boundIds = bindList exp
       case (v `elem` boundIds) of
         True -> return exp
         _    -> case (null $ List.intersect boundIds (freeIds expReplacement)) of
                  True -> recT (\ _ -> (substR v expReplacement)) Rec
                  _    -> return exp



letSubstR :: RewriteH CoreExpr
letSubstR = rewrite $ \ c exp ->
    case exp of
      (Let (NonRec b be) e) -> do  apply (substR b be) c e
      _ -> fail "LetSubst failed. Expr is not a Non-recursive Let."

-- tests ...
alphaCase :: RewriteH CoreExpr
alphaCase = caseT idR (\ _ -> alphaAlt) Case
