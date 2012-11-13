{-# LANGUAGE TypeFamilies, FlexibleContexts #-}
module Language.HERMIT.Primitive.AlphaConversion
       ( -- * Alpha-Renaming and Shadowing
         externals
         -- ** Alpha-Renaming
       , alpha
       , alphaLam
       , alphaCaseBinder
       , alphaAltIds
       , alphaAlt
       , alphaCase
       , alphaLetVars
       , alphaLetRecIds
       , alphaLetOne
       , alphaLet
       , alphaConsOne
       , alphaCons
         -- ** Shadow Detection and Unshadowing
       , unshadow
       , visibleVarsT
       , freshNameGenT
       , freshNameGenAvoiding
       , replaceVarR
       )
where

import GhcPlugins hiding (empty)

import Control.Applicative
import Control.Arrow
import Data.Char (isDigit)
import Data.List (nub)
import Data.Monoid

import Language.HERMIT.Core
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External

import Language.HERMIT.Primitive.GHC hiding (externals)
import Language.HERMIT.Primitive.Common

import qualified Language.Haskell.TH as TH

import Prelude hiding (exp)

-----------------------------------------------------------------------

-- | Externals for alpha-renaming.
externals :: [External]
externals = map (.+ Deep)
         [  external "alpha" alpha
               [ "renames the bound variables at the current node."]
         ,  external "alpha-lam" (promoteExprR . alphaLam . Just)
               [ "renames the bound variable in a Lambda expression to the given name."]
         ,  external "alpha-lam" (promoteExprR $ alphaLam Nothing)
               [ "renames the bound variable in a Lambda expression."]
         ,  external "alpha-case-binder" (promoteExprR . alphaCaseBinder . Just)
               [ "renames the binder in a Case expression to the given name."]
         ,  external "alpha-case-binder" (promoteExprR $ alphaCaseBinder Nothing)
               [ "renames the binder in a Case expression."]
         ,  external "alpha-alt" (promoteAltR alphaAlt)
               [ "renames all binders in a Case alternative."]
         ,  external "alpha-case" (promoteExprR alphaCase)
               [ "renames all binders in a Case alternative."]
         ,  external "alpha-let" (promoteExprR . alphaLetOne . Just)
               [ "renames the bound variable in a Let expression with one binder to the given name."]
         ,  external "alpha-let" (promoteExprR alphaLet)
               [ "renames the bound variables in a Let expression."]
         ,  external "alpha-top" (promoteProgR . alphaConsOne . Just)
               [ "renames the bound variable in a top-level binding with one binder to the given name."]
         ,  external "alpha-top" (promoteProgR alphaCons)
               [ "renames the bound variables in a top-level binding."]
         , external "unshadow" unshadow
                [ "Rename local variables with manifestly unique names (x, x0, x1, ...)."]
         ]

-----------------------------------------------------------------------
--
-- freshNameGen is a function used in conjunction with cloneVarH, which clones an existing 'Var'.
-- But, what name should the new Id have?
-- cloneVarH generates a new Unique -- so we are positive that the new Var will be new,
-- but freshNameGen tries to assign a Name that will be meaningful to the user, and
-- not shadow other names in scope.
-- So,  we start with the name of the original Id, and add an integer suffix
--  x  goes to x0 or x1 or ...
-- and we do not want this newly generated name to shadow either:
-- 1.  Any free variable name in the active Expr; or
-- 2.  Any bound variables in context.

-- | List all visible identifiers (in the expression or the context).
visibleVarsT :: TranslateH CoreExpr [Var]
visibleVarsT = boundVarsT `mappend` freeVarsT

-- | If a name is provided replace the string with that,
--   otherwise modify the string making sure to /not/ clash with any visible variables.
freshNameGenT :: Maybe TH.Name -> TranslateH CoreExpr (String -> String)
freshNameGenT mn = freshNameGenAvoiding mn <$> visibleVarsT

-- | A generalisation of 'freshNameGen' that operates on any node, but only avoids name clashes with the results of the argument translation.
freshNameGenAvoiding :: Maybe TH.Name -> [Var] -> (String -> String)
freshNameGenAvoiding mn vs str = maybe (inventNames vs str) TH.nameBase mn

-- | Invent a new String based on the old one, but avoiding clashing with the given list of identifiers.
inventNames :: [Var] -> String -> String
inventNames curr old = head
                     [ nm
                     | nm <- old : [ base ++ show uq | uq <- [start ..] :: [Int] ]
                     , nm `notElem` names
                     ]
   where
           names = nub (map getOccString curr)
           nums = reverse $ takeWhile isDigit (reverse old)
           baseLeng = length $ drop (length nums) old
           base = take baseLeng old
           start = case reads nums of
                     [(v,_)] -> v + 1
                     _       -> 0


-- | Remove all variables from the first list that shadow a variable in the second list.
shadowedBy :: [Var] -> [Var] -> [Var]
shadowedBy vs fvs = filter (\ v -> getOccString v `elem` map getOccString fvs) vs

-- | Lifted version of 'shadowedBy'.
--   Additionally, it fails if no shadows are found.
shadowedByT :: TranslateH a [Var] -> TranslateH a [Var] -> TranslateH a [Var]
shadowedByT t1 t2 = (shadowedBy <$> t1 <*> t2) >>> acceptR (not . null) "No shadowing detected."

-- | Rename local variables with manifestly unique names (x, x0, x1, ...).
--   Does not rename top-level definitions (though this may change in the future).
unshadow :: RewriteH Core
unshadow = setFailMsg "No shadows to eliminate." $
           anytdR (promoteExprR unshadowExpr <+ promoteAltR unshadowAlt)

  where
    unshadowExpr :: RewriteH CoreExpr
    unshadowExpr = do vs <- shadowedByT (boundVarsT `mappend` freeVarsT) (letVarsT <+ fmap return (caseWildVarT <+ lamVarT))
                      alphaLam Nothing <+ alphaLetRecIds vs <+ alphaLetNonRec Nothing <+ alphaCaseBinder Nothing

    unshadowAlt :: RewriteH CoreAlt
    unshadowAlt = shadowedByT altVarsT (boundVarsT `mappend` altFreeVarsT) >>= alphaAltIds

-----------------------------------------------------------------------

-- | Replace all occurrences of a specified variable.
--   Arguments are the variable to replace and the replacement variable, respectively.
replaceVarR :: (Injection a Core, Generic a ~ Core) => Var -> Var -> RewriteH a
replaceVarR v v' = extractR $ tryR $ substR v (Var v')

-- | Given a variable to replace, and a replacement, produce a 'Var' @->@ 'Var' function that
--   acts as in identity for all 'Var's except the one to replace, for which it returns the replacment.
--   Don't export this, it'll likely just cause confusion.
replaceVar :: Var -> Var -> (Var -> Var)
replaceVar v v' i = if v == i then v' else i

-----------------------------------------------------------------------

-- | Alpha rename a lambda binder.  Optionally takes a suggested new name.
alphaLam :: Maybe TH.Name -> RewriteH CoreExpr
alphaLam mn = setFailMsg (wrongFormForAlpha "Lam v e") $
              do (v, nameModifier) <- lamT (freshNameGenT mn) (,)
                 v' <- constT (cloneVarH nameModifier v)
                 lamT (replaceVarR v v') (\ _ -> Lam v')

-----------------------------------------------------------------------

-- | Alpha rename a case binder.  Optionally takes a suggested new name.
alphaCaseBinder :: Maybe TH.Name -> RewriteH CoreExpr
alphaCaseBinder mn = setFailMsg (wrongFormForAlpha "Case e v ty alts") $
                     do Case _ v _ _ <- idR
                        nameModifier <- freshNameGenT mn
                        v' <- constT (cloneVarH nameModifier v)
                        caseT idR (\ _ -> replaceVarR v v') (\ e _ t alts -> Case e v' t alts)

-----------------------------------------------------------------------

-- | Rename the specified identifier in a case alternative.  Optionally takes a suggested new name.
alphaAltId :: Maybe TH.Name -> Id -> RewriteH CoreAlt
alphaAltId mn v = do nameModifier <- altT (freshNameGenT mn) (\ _ _ nameGen -> nameGen)
                     v' <- constT (cloneVarH nameModifier v)
                     altT (replaceVarR v v') (\ con vs e -> (con, map (replaceVar v v') vs, e))

-- | Rename the specified identifiers in a case alternative.
alphaAltIds :: [Id] -> RewriteH CoreAlt
alphaAltIds = andR . map (alphaAltId Nothing)

-- | Rename all identifiers bound in a case alternative.
alphaAlt :: RewriteH CoreAlt
alphaAlt = altVarsT >>= alphaAltIds

-----------------------------------------------------------------------

-- | Rename all identifiers bound in a case expression.
alphaCase :: RewriteH CoreExpr
alphaCase = alphaCaseBinder Nothing >+> caseAnyR (fail "") (const alphaAlt)

-----------------------------------------------------------------------

-- | Alpha rename a non-recursive let binder.  Optionally takes a suggested new name.
alphaLetNonRec :: Maybe TH.Name -> RewriteH CoreExpr
alphaLetNonRec mn = setFailMsg (wrongFormForAlpha "Let (NonRec v e1) e2") $
                    do (v, nameModifier) <- letNonRecT idR (freshNameGenT mn) (\ v _ nameMod -> (v, nameMod))
                       v' <- constT (cloneVarH nameModifier v)
                       letNonRecT idR (replaceVarR v v') (\ _ e1 e2 -> Let (NonRec v' e1) e2)

-- | Alpha rename a non-recursive let binder if the variable appears in the argument list.  Optionally takes a suggested new name.
alphaLetNonRecVars :: Maybe TH.Name -> [Var] -> RewriteH CoreExpr
alphaLetNonRecVars mn vs = whenM ((`elem` vs) <$> letNonRecVarT) (alphaLetNonRec mn)

-- | Rename the specified identifier bound in a recursive let.  Optionally takes a suggested new name.
alphaLetRecId :: Maybe TH.Name -> Id -> RewriteH CoreExpr
alphaLetRecId mn v = setFailMsg (wrongFormForAlpha "Let (Rec bs) e") $
                     do usedVars <- boundVarsT `mappend`
                                    letVarsT  `mappend`
                                    letRecDefT (\ _ -> freeVarsT) freeVarsT (\ bndfvs vs -> concatMap snd bndfvs ++ vs)
                        v' <- constT (cloneVarH (freshNameGenAvoiding mn usedVars) v)
                        letRecDefT (\ _ -> replaceVarR v v')
                                   (replaceVarR v v')
                                   (\ bs e -> Let (Rec $ (map.first) (replaceVar v v') bs) e)

-- | Rename the specified identifiers bound in a recursive let.
alphaLetRecIds :: [Id] -> RewriteH CoreExpr
alphaLetRecIds = andR . map (alphaLetRecId Nothing)

-- | Rename the specified variables bound in a let.
alphaLetVars :: [Var] -> RewriteH CoreExpr
alphaLetVars vs = alphaLetNonRecVars Nothing vs <+ alphaLetRecIds vs

-- | Rename all identifiers bound in a recursive let.
alphaLetRec :: RewriteH CoreExpr
alphaLetRec = setFailMsg (wrongFormForAlpha "Let (Rec bs) e") $
              letRecVarsT >>= alphaLetRecIds

-- | Rename the identifier bound in a recursive let with a single recursively bound identifier.  Optionally takes a suggested new name.
alphaLetRecOne :: Maybe TH.Name -> RewriteH CoreExpr
alphaLetRecOne mn = setFailMsg (wrongFormForAlpha "Let (Rec [(v,e1)]) e2") $
                    do Let (Rec [(v, _)]) _ <- idR
                       alphaLetRecId mn v

-- | Rename the identifier bound in a let with a single bound identifier.  Optionally takes a suggested new name.
alphaLetOne :: Maybe TH.Name -> RewriteH CoreExpr
alphaLetOne mn = alphaLetNonRec mn <+ alphaLetRecOne mn

-- | Rename all identifiers bound in a Let.
alphaLet :: RewriteH CoreExpr
alphaLet = alphaLetRec <+ alphaLetNonRec Nothing

-----------------------------------------------------------------------

-- | Alpha rename a non-recursive top-level binder.  Optionally takes a suggested new name.
alphaConsNonRec :: Maybe TH.Name -> RewriteH CoreProg
alphaConsNonRec mn = setFailMsg (wrongFormForAlpha "ProgCons (NonRec v e) p") $
                     do ProgCons (NonRec v _) _ <- idR
                        nameModifier <- consNonRecT (freshNameGenT mn) idR (\ _ nameGen _ -> nameGen)
                        v' <- constT (cloneVarH nameModifier v)
                        consNonRecT idR (replaceVarR v v') (\ _ e1 e2 -> ProgCons (NonRec v' e1) e2)

-- | Rename the specified identifier bound in a recursive top-level binder.  Optionally takes a suggested new name.
alphaConsRecId :: Maybe TH.Name -> Id -> RewriteH CoreProg
alphaConsRecId mn v = setFailMsg (wrongFormForAlpha "ProgCons (Rec bs) p") $
                      do usedVars <- boundVarsT `mappend`
                                     progConsT recVarsT (return ()) (\ vs () -> vs) `mappend`
                                     consRecDefT (\ _ -> freeVarsT) idR (\ bndfvs _ -> concatMap snd bndfvs)
                         v' <- constT (cloneVarH (freshNameGenAvoiding mn usedVars) v)
                         consRecDefT (\ _ -> replaceVarR v v')
                                     (replaceVarR v v')
                                     (\ bs e -> ProgCons (Rec $ (map.first) (replaceVar v v') bs) e)

-- | Rename the specified identifiers bound in a program node containing a recursive binding group.
alphaConsRecIds :: [Id] -> RewriteH CoreProg
alphaConsRecIds = andR . map (alphaConsRecId Nothing)

-- | Rename all identifiers bound in a recursive top-level binder.
alphaConsRec :: RewriteH CoreProg
alphaConsRec = setFailMsg (wrongFormForAlpha "ProgCons (Rec bs) p") $
               progConsT recVarsT mempty (\ vs () -> vs) >>= alphaConsRecIds

-- | Rename the identifier bound in a recursive top-level binder with a single recursively bound identifier.  Optionally takes a suggested new name.
alphaConsRecOne :: Maybe TH.Name -> RewriteH CoreProg
alphaConsRecOne mn = setFailMsg (wrongFormForAlpha "ProgCons (Rec [Def v e]) p") $
                     do ProgCons (Rec [(v, _)]) _ <- idR
                        alphaConsRecId mn v

-- | Rename the identifier bound in a top-level binder with a single bound identifier.  Optionally takes a suggested new name.
alphaConsOne :: Maybe TH.Name -> RewriteH CoreProg
alphaConsOne mn = alphaConsNonRec mn <+ alphaConsRecOne mn

-- | Rename all identifiers bound in a Let.
alphaCons :: RewriteH CoreProg
alphaCons = alphaConsRec <+ alphaConsNonRec Nothing

-----------------------------------------------------------------------

-- | Alpha rename any bindings at this node.  Note: does not rename case alternatives unless invoked on the alternative.
alpha :: RewriteH Core
alpha = setFailMsg "Cannot alpha-rename here." $
           promoteExprR (alphaLam Nothing <+ alphaCaseBinder Nothing <+ alphaLet)
        <+ promoteProgR alphaCons
        <+ promoteAltR alphaAlt

-----------------------------------------------------------------------

wrongFormForAlpha :: String -> String
wrongFormForAlpha s = "Cannot alpha-rename, " ++ wrongExprForm s

-----------------------------------------------------------------------
