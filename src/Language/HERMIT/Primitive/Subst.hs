{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

module Language.HERMIT.Primitive.Subst where

import GhcPlugins hiding ((<>))
import qualified Data.Map as Map
import qualified Data.List as List

import Language.KURE
import Control.Applicative

import Language.HERMIT.HermitMonad
import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv as Env
import Language.HERMIT.External

import qualified Language.Haskell.TH as TH


externals :: [External]
externals = map (.+ Experiment)
         [
           external "alpha" (promoteR alphaLambda)
                [ "Alpha rename (for Lambda's)."]
         , external "alpha-let" (promoteR alphaLet)
                [ "Alpha rename (for Let)."]
         , external "let-sub" (promoteR letSubstR)
                [ "Let substitution."]

           -- the remaining are really just for testing.
         , external "alpha-alt" (promoteR alphaAlt)
                [ "Alpha rename (for a single Case Alternative)."]
         , external "alpha-case" (promoteR alphaCase)
                [ "Alpha renaming for each alternative of a Case.."]
         ]

bindList :: Bind Id -> [Id]
bindList (NonRec b _) = [b]

bindList (Rec binds) = map fst binds


varNameH :: Id -> TH.Name
varNameH = TH.mkName . showSDoc . ppr

freshVarT :: Id -> TranslateH a Id
freshVarT v = constMT $ newVarH (varNameH v) (idType v)

-- The alpha renaming functions defined here,
-- rely on a function to return a globally fresh Id,
-- therefore, they do not require a list of Id's which must not clash.

alphaLambda :: RewriteH CoreExpr
alphaLambda = do (Lam b e) <- idR
                 b' <- freshVarT b
                 lamT (substR b $ Var b') (\ _ -> Lam b')


-- Replace each var bound in a let expr with a globally fresh Id.
alphaLet :: RewriteH CoreExpr
alphaLet = alphaNonRecLet <+ alphaRecLet

alphaNonRecLet :: RewriteH CoreExpr
alphaNonRecLet = do Let (NonRec v e1) e2 <- idR
                    v' <- freshVarT v
                    letNonRecT idR (substR v $ Var v') (\ _ e1 e2 -> Let (NonRec v' e1) e2)

alphaRecLet :: RewriteH CoreExpr
alphaRecLet = do (Let bds@(Rec _) e) <- idR
                 let boundIds = bindList bds
                 freshBoundIds <- sequence $ fmap freshVarT boundIds
                 letRecDefT (\ _ -> (foldr seqSubst idR (zip boundIds freshBoundIds)))
                            (foldr seqSubst idR (zip boundIds freshBoundIds))
                            (\ bds' e' -> let freshBds = zip freshBoundIds (map snd bds') in (Let (Rec freshBds) e'))
    where seqSubst (v,v') t = t >-> (substR v $ Var v')

-- there is no alphaCase.
-- instead alphaAlt performs renaming over an individual Case alternative
alphaAlt :: RewriteH CoreAlt
alphaAlt = do (con, vs, e) <- idR
              freshBoundIds <- sequence $ fmap freshVarT vs
              altT (foldr seqSubst idR (zip vs freshBoundIds)) (\ _ _ e' -> (con, freshBoundIds, e'))
    where seqSubst (v,v') t = t >-> (substR v $ Var v')

-- Andy's substitution rewrite
--  E [ v::r ] ===   let (NonRec v = r) in E
--      and then inline "v"


-- | Substitution

substR :: Id -> CoreExpr  -> RewriteH CoreExpr
substR v expReplacement = (rule12 <+ rule345 <+ rule78 <+ rule9)  <+ rule6
    where -- The 6 rules from the textbook for the simple lambda calculus.
        rule12 :: RewriteH CoreExpr
        rule12 = do (Var n0) <- idR
                    if (n0 == v)
                    then return expReplacement
                    else idR

        rule345 :: RewriteH CoreExpr
        rule345 = do (Lam b e) <- idR
                     whenT (b == v) idR
                       <+ whenT (v `notElem` freeIds e) idR
                       <+ whenT (b `notElem` freeIds expReplacement)
                                (lamT (substR v expReplacement) Lam)
                       <+ alphaLambda  >-> rule345

        rule6 = allR (promoteR $ substR v expReplacement)
        -- like Rule 3 and 4/5 above, but for lets
        rule78 :: RewriteH CoreExpr
        rule78 = do (Let bds e) <- idR
                    whenT (v `elem` (bindList bds)) idR
                       <+ whenT (null $ List.intersect (bindList bds) (freeIds expReplacement))
                                (letT (substBindR v expReplacement)  (substR v expReplacement)  Let)
                             -- If v is not free in e, it may be free in the expression(s) bound by the let
                       <+ whenT (v `notElem` freeIds e)
                                (letT (substBindR v expReplacement) idR Let)
                             -- final case.  v is free in e, but the bound var(s) in the let appear
                             -- free in the replacement expression.  Alpha renaming to the rescue, and try again.
                       <+ alphaLet  >-> rule78

        -- edk?  Do we need to worry about clashes with the VBind component of a Case?
        --  For now, it is ignored here.
        rule9 = caseT (substR v expReplacement) (\_ -> substAltR v expReplacement) Case

-- edk !! Note, this subst handles name clashes with variables bound in the Alt form,
-- since the scope of these bound variables is within the Alt.
substAltR :: Id -> CoreExpr -> RewriteH CoreAlt
substAltR v expReplacement =
    do (con, bs, e) <- idR
       whenT (v `elem` bs) idR
          <+ whenT (null $ List.intersect bs (freeIds expReplacement))
                   (altT (substR v expReplacement)  (,,))
          <+ alphaAlt >-> (substAltR v expReplacement)


-- edk !! Note, this subst DOES NOT handle name clashes with variables bound in the Bind form,
-- since the scope of these bound variables extends beyond the form.
-- IF there is a name clash, the Bind is returned un-altered, rather than failure.
substBindR :: Id -> CoreExpr  -> RewriteH CoreBind
substBindR v expReplacement = (substNonRecBindR v expReplacement) <+ (substRecBindR v expReplacement)

substNonRecBindR :: Id -> CoreExpr  -> RewriteH CoreBind
substNonRecBindR v expReplacement =
    do (NonRec b e) <- idR
       whenT (b == v) idR
         <+ whenT (b `elem` (freeIds expReplacement)) idR
         <+ (nonRecT (substR v expReplacement) NonRec)

substRecBindR :: Id -> CoreExpr  -> RewriteH CoreBind
substRecBindR v expReplacement =
    do exp@(Rec bds) <- idR
       let boundIds = bindList exp
       whenT (v `elem` boundIds) idR
         <+ whenT (not . null $ List.intersect boundIds (freeIds expReplacement)) idR
         <+ (recDefT (\ _ -> (substR v expReplacement)) Rec)

letSubstR :: RewriteH CoreExpr
letSubstR = rewrite $ \ c exp ->
    case exp of
      (Let (NonRec b be) e)
         | isId b    -> apply (substR b be) c e
         -- For type subst, we use the GHC subst mechansim
      (Let (NonRec b (Type bty)) e)
         | isTyVar b -> do
                let sub = extendTvSubst emptySubst b bty
                return $ substExpr (text "letSubstR") sub e
--         | otherwise -> fail "LetSubst failed. (is a type variable)"
      _ -> fail "LetSubst failed. Expr is not a Non-recursive Let."

-- tests ...
alphaCase :: RewriteH CoreExpr
alphaCase = caseT idR (\ _ -> alphaAlt) Case
