{-# LANGUAGE TypeFamilies, FlexibleInstances #-}
-- TODO: remove this module
module Language.HERMIT.Primitive.Subst where

import GhcPlugins hiding (empty)
import qualified Data.List as List

import Control.Arrow

import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.Primitive.GHC(coreExprFreeIds)

import qualified Language.Haskell.TH as TH

import Prelude hiding (exp)
import Data.Maybe

externals :: [External]
externals =
         [
           external "alpha" (\nm -> promoteR (alphaLambda (Just nm)) :: RewriteH Core)
                [ "alpha 'v renames the bound variable in a Lambda expression to v."]
         , external "alpha" (promoteR (alphaLambda Nothing) :: RewriteH Core)
                [ "renames the bound variable in a lambda expression."]
         , external "alpha-let" (promoteR alphaLet :: RewriteH Core)
                [ "Alpha rename for any Let expr."]
         , external "alpha-let-nonrec" (\nm -> promoteR (alphaNonRecLet (Just nm)) :: RewriteH Core)
                [ "alpha-let-nonrec 'v renames the bound variable in a NonRecursive Let expression to v."]
         , external "alpha-let-rec1" (\nm -> promoteR (alphaRecLetOne (Just nm)) :: RewriteH Core)
                [ "alpha-let-rec1 'v renames the bound variable in a Recursive Let expression (with a single binding) to v."]

           -- the remaining are really just for testing.
         , external "alpha-alt" (promoteR alphaAlt :: RewriteH Core)
                [ "Alpha rename (for a single Case Alternative)."]
         , external "alpha-case" (promoteR alphaCase :: RewriteH Core)
                [ "Alpha renaming for each alternative of a Case."]
         ]

bindList :: Bind Id -> [Id]
bindList (NonRec b _) = [b]

bindList (Rec binds) = map fst binds


newVarName :: Id -> TH.Name
newVarName x = TH.mkName $ (showSDoc (ppr x) ++ "New")

freshVarT :: Id -> TranslateH a Id
freshVarT v = constT $ newVarH (newVarName v) (idType v)

freshVarT' :: TH.Name -> Type -> TranslateH a Id
freshVarT' nm ty  = constT $ newVarH nm ty


-- The alpha renaming functions defined here,
-- rely on a function to return a globally fresh Id,
-- therefore, they do not require a list of Id's which must not clash.

alphaLambda :: Maybe TH.Name -> RewriteH CoreExpr
alphaLambda nm = do Lam b _ <- idR
                    let newname = fromMaybe (newVarName b) nm
                    b' <- freshVarT' newname (idType b)
                    lamT (trySubstR b $ Var b') (\ _ -> Lam b')

-- Replace each var bound in a let expr with a globally fresh Id.
alphaLet :: RewriteH CoreExpr
alphaLet = alphaNonRecLet Nothing <+ alphaRecLet

alphaNonRecLet :: Maybe TH.Name -> RewriteH CoreExpr
alphaNonRecLet nm = do Let (NonRec v _) _ <- idR
                       let newname = fromMaybe (newVarName v) nm
                       v' <- freshVarT' newname (idType v)
                       letNonRecT idR (trySubstR v $ Var v') (\ _ e1 e2 -> Let (NonRec v' e1) e2)

alphaRecLet :: RewriteH CoreExpr
alphaRecLet = do Let bds@(Rec _) _ <- idR
                 let boundIds = bindList bds
                 freshBoundIds <- sequence $ fmap freshVarT boundIds
                 letRecDefT (\ _ -> (foldr seqSubst idR (zip boundIds freshBoundIds)))
                            (foldr seqSubst idR (zip boundIds freshBoundIds))
                            (\ bds' e' -> let freshBds = zip freshBoundIds (map snd bds') in Let (Rec freshBds) e')
    where seqSubst (v,v') t = t >>> (trySubstR v $ Var v')


alphaRecLetOne :: Maybe TH.Name -> RewriteH CoreExpr
alphaRecLetOne nm = do Let (Rec [(v, _)]) _ <- idR
                       let newname = fromMaybe (newVarName v) nm
                       v' <- freshVarT' newname (idType v)
                       letRecDefT (\ _ -> (trySubstR v $ Var v'))
                                  (trySubstR v $ Var v')
                                  (\ [(_,be)] e' -> Let (Rec [(v', be)]) e')

-- there is no alphaCase.
-- instead alphaAlt performs renaming over an individual Case alternative
alphaAlt :: RewriteH CoreAlt
alphaAlt = do (con, vs, _) <- idR
              freshBoundIds <- sequence $ fmap freshVarT vs
              altT (foldr seqSubst idR (zip vs freshBoundIds)) (\ _ _ e' -> (con, freshBoundIds, e'))
    where seqSubst (v,v') t = t >>> (trySubstR v $ Var v')

-- Andy's substitution rewrite
--  E [ v::r ] ===   let (NonRec v = r) in E
--      and then inline "v"


-- | Substitution

-- for when we want to consider no change to be a success
trySubstR :: Id -> CoreExpr -> RewriteH CoreExpr
trySubstR v e = tryR (substR v e)

substR :: Id -> CoreExpr -> RewriteH CoreExpr
substR v expReplacement = (rule12 <+ rule345 <+ rule78 <+ rule9)  <+ rule6
    where -- The 6 rules from the textbook for the simple lambda calculus.
        rule12 :: RewriteH CoreExpr
        rule12 = whenM (varT (==v)) (return expReplacement)

        rule345 :: RewriteH CoreExpr
        rule345 = do Lam b e <- idR
                     guardMsg (b == v) "Subtitution var clashes with Lam"
                     guardMsg (v `notElem` coreExprFreeIds e) "Substitution var not used in body of Lam"
                     if b `elem` coreExprFreeIds expReplacement
                      then alphaLambda Nothing >>> rule345
                      else lamR (substR v expReplacement)

        rule6 = anyR (promoteExprR $ substR v expReplacement)
        -- like Rule 3 and 4/5 above, but for lets
        rule78 :: RewriteH CoreExpr
        rule78 = do Let bds _e <- idR
                    guardMsg (v `elem` bindList bds) "Substitution var clashes with Let var"
                    if null $ List.intersect (bindList bds) (coreExprFreeIds expReplacement)
                     then letAnyR (substBindR v expReplacement) (substR v expReplacement)
                     else alphaLet >>> rule78

        -- edk?  Do we need to worry about clashes with the VBind component of a Case?
        --  For now, it is ignored here.
        rule9 = caseAnyR (substR v expReplacement) (\_ -> substAltR v expReplacement)

-- edk !! Note, this subst handles name clashes with variables bound in the Alt form,
-- since the scope of these bound variables is within the Alt.
substAltR :: Id -> CoreExpr -> RewriteH CoreAlt
substAltR v expReplacement =
    do (_, bs, _) <- idR
       guardMsg (v `elem` bs) "Substitution var clashes with Alt binders"
       if null $ List.intersect bs (coreExprFreeIds expReplacement)
        then altR (substR v expReplacement)
        else alphaAlt >>> altR (substR v expReplacement)


-- edk !! Note, this subst DOES NOT handle name clashes with variables bound in the Bind form,
-- since the scope of these bound variables extends beyond the form.
-- IF there is a name clash, the Bind is returned un-altered, rather than failure.
substBindR :: Id -> CoreExpr -> RewriteH CoreBind
substBindR v expReplacement = substNonRecBindR v expReplacement <+ substRecBindR v expReplacement

substNonRecBindR :: Id -> CoreExpr  -> RewriteH CoreBind
substNonRecBindR v expReplacement =
    do NonRec b _ <- idR
       guardMsg (b == v) "Substitution var clashes wth Let bound var"
       guardMsg (b `elem` coreExprFreeIds expReplacement) "Let bound var is free in substitution expr."
       nonRecR (substR v expReplacement)

substRecBindR :: Id -> CoreExpr  -> RewriteH CoreBind
substRecBindR v expReplacement =
    do exp@(Rec _) <- idR
       let boundIds = bindList exp
       guardMsg (v `elem` boundIds) "Substitution var clashes wth Let bound var"
       guardMsg (not . null $ List.intersect boundIds (coreExprFreeIds expReplacement)) "Let bound var is free in substitution expr."
       recDefAnyR (\ _ -> substR v expReplacement)

letSubstR :: RewriteH CoreExpr
letSubstR = rewrite $ \ c exp ->
    case exp of
      Let (NonRec b be) e | isId b -> apply (substR b be) c e
         -- For type subst, we use the GHC subst mechansim
      Let (NonRec b (Type bty)) e | isTyVar b -> do
                let sub = extendTvSubst emptySubst b bty
                return $ substExpr (text "letSubstR") sub e
--         | otherwise -> fail "LetSubst failed. (is a type variable)"
      _ -> fail "LetSubst failed. Expr is not a Non-recursive Let."

-- tests ...
alphaCase :: RewriteH CoreExpr
alphaCase = caseAnyR (fail "alphaCase") (\ _ -> alphaAlt)
