{-# LANGUAGE FlexibleContexts #-}
module Language.HERMIT.Primitive.AlphaConversion
       ( -- * Alpha-Renaming and Shadowing
         externals
         -- ** Alpha-Renaming
       , alpha
       , alphaLam
       , alphaCaseBinder
       , alphaAltWith
       , alphaAltVars
       , alphaAlt
       , alphaCase
       , alphaLetWith
       , alphaLetVars
       , alphaLet
       , alphaConsWith
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
import Data.Maybe (fromMaybe, listToMaybe)
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
               [ "Renames the bound variables at the current node."]
         ,  external "alpha-lam" (promoteExprR . alphaLam . Just)
               [ "Renames the bound variable in a Lambda expression to the given name."]
         ,  external "alpha-lam" (promoteExprR $ alphaLam Nothing)
               [ "Renames the bound variable in a Lambda expression."]
         ,  external "alpha-case-binder" (promoteExprR . alphaCaseBinder . Just)
               [ "Renames the binder in a Case expression to the given name."]
         ,  external "alpha-case-binder" (promoteExprR $ alphaCaseBinder Nothing)
               [ "Renames the binder in a Case expression."]
         ,  external "alpha-alt" (promoteAltR alphaAlt)
               [ "Renames all binders in a Case alternative."]
         ,  external "alpha-alt" (promoteAltR . alphaAltWith)
               [ "Renames all binders in a Case alternative using the user-provided list of new names."]
         ,  external "alpha-case" (promoteExprR alphaCase)
               [ "Renames all binders in a Case alternative."]
         ,  external "alpha-let" (promoteExprR . alphaLetWith)
               [ "Renames the bound variables in a Let expression using a list of suggested names."]
         ,  external "alpha-let" (promoteExprR alphaLet)
               [ "Renames the bound variables in a Let expression."]
         ,  external "alpha-top" (promoteProgR . alphaConsWith)
               [ "Renames the bound identifiers in the top-level binding group at the head of the program using a list of suggested names."]
         -- ,  external "alpha-top" (promoteProgR alphaCons)
         --       [ "Renames the bound identifiers in the top-level binding at the head of the program."]
         -- ,  external "alpha-program" (promoteProgR alphaProg)
         --       [ "Renames identifiers bound at the top-level of the program."]
         ,  external "unshadow" unshadow
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

-- | Use the optional argument if given, otherwise generate a new name avoiding clashes with the list of variables.
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
shadowedByT t1 t2 = setFailMsg "No shadows detected." $ (shadowedBy <$> t1 <*> t2) >>> acceptR (not . null)

-- | Rename local variables with manifestly unique names (x, x0, x1, ...).
--   Does not rename top-level definitions.
unshadow :: RewriteH Core
unshadow = setFailMsg "No shadows to eliminate." $
           anytdR (promoteExprR unshadowExpr <+ promoteAltR unshadowAlt)

  where
    unshadowExpr :: RewriteH CoreExpr
    unshadowExpr = do vs <- shadowedByT (boundVarsT `mappend` freeVarsT) (letVarsT <+ fmap return (caseWildIdT <+ lamVarT))
                      alphaLam Nothing <+ alphaLetVars vs <+ alphaCaseBinder Nothing

    unshadowAlt :: RewriteH CoreAlt
    unshadowAlt = shadowedByT altVarsT (boundVarsT `mappend` altFreeVarsT) >>= alphaAltVars

-----------------------------------------------------------------------

-- | Replace all occurrences of a specified variable.
--   Arguments are the variable to replace and the replacement variable, respectively.
replaceVarR :: (Injection a Core) => Var -> Var -> RewriteH a
replaceVarR v v' = extractR $ tryR $ substR v $ varToCoreExpr v'

-- | Given a variable to replace, and a replacement, produce a 'Var' @->@ 'Var' function that
--   acts as in identity for all 'Var's except the one to replace, for which it returns the replacment.
--   Don't export this, it'll likely just cause confusion.
replaceVar :: Var -> Var -> (Var -> Var)
replaceVar v v' = replaceVars [(v,v')]

-- | Given a lists of variables to replace, and their replacements, produce a 'Var' @->@ 'Var' function that
--   acts as in identity for all 'Var's except the ones to replace, for which it returns the replacment.
--   Don't export this, it'll likely just cause confusion.
replaceVars :: [(Var,Var)] -> (Var -> Var)
replaceVars kvs v = fromMaybe v (lookup v kvs)

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

-- | Rename the specified variable in a case alternative.  Optionally takes a suggested new name.
alphaAltVar :: Maybe TH.Name -> Var -> RewriteH CoreAlt
alphaAltVar mn v = do nameModifier <- altT (freshNameGenT mn) (\ _ _ nameGen -> nameGen)
                      v' <- constT (cloneVarH nameModifier v)
                      altT (replaceVarR v v') (\ con vs e -> (con, map (replaceVar v v') vs, e))

-- | Rename the specified variables in a case alternative, using the suggested names where provided.
alphaAltVarsWith :: [(Maybe TH.Name,Var)] -> RewriteH CoreAlt
alphaAltVarsWith = andR . map (uncurry alphaAltVar)

-- | Rename the variables bound in a case alternative with the given list of suggested names.
alphaAltWith :: [TH.Name] -> RewriteH CoreAlt
alphaAltWith ns = do vs <- altVarsT
                     alphaAltVarsWith $ zip (map Just ns) vs

-- | Rename the specified variables in a case alternative.
alphaAltVars :: [Var] -> RewriteH CoreAlt
alphaAltVars = alphaAltVarsWith . zip (repeat Nothing)

-- | Rename all identifiers bound in a case alternative.
alphaAlt :: RewriteH CoreAlt
alphaAlt = altVarsT >>= alphaAltVars

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

-- | Rename the specified identifiers in a recursive let, using the suggested names where provided.
alphaLetRecIdsWith :: [(Maybe TH.Name,Id)] -> RewriteH CoreExpr
alphaLetRecIdsWith = andR . map (uncurry alphaLetRecId)

-- | Rename the identifiers bound in a Let with the given list of suggested names.
alphaLetWith :: [TH.Name] -> RewriteH CoreExpr
alphaLetWith ns = alphaLetNonRec (listToMaybe ns)
                  <+ (letRecIdsT >>= (alphaLetRecIdsWith . zip (map Just ns)))

-- | Rename the specified variables bound in a let.
alphaLetVars :: [Var] -> RewriteH CoreExpr
alphaLetVars vs = alphaLetNonRecVars Nothing vs <+ alphaLetRecIdsWith (zip (repeat Nothing) vs)

-- | Rename all identifiers bound in a Let.
alphaLet :: RewriteH CoreExpr
alphaLet = letVarsT >>= alphaLetVars

-----------------------------------------------------------------------

-- | Alpha rename a non-recursive top-level binder.  Optionally takes a suggested new name.
alphaConsNonRec :: TH.Name -> RewriteH CoreProg
alphaConsNonRec n = setFailMsg (wrongFormForAlpha "ProgCons (NonRec v e) p") $
                    do ProgCons (NonRec v _) _ <- idR
                       v' <- constT (cloneVarH (\ _ -> TH.nameBase n) v)
                       consNonRecT idR (replaceVarR v v') (\ _ e1 e2 -> ProgCons (NonRec v' e1) e2)

-- -- | Alpha rename a non-recursive top-level binder if the identifier appears in the argument list.  Optionally takes a suggested new name.
-- alphaConsNonRecIds :: Maybe TH.Name -> [Id] -> RewriteH CoreProg
-- alphaConsNonRecIds mn vs = whenM ((`elem` vs) <$> consNonRecIdT) (alphaConsNonRec mn)

-- | Rename the specified identifier bound in a recursive top-level binder.  Optionally takes a suggested new name.
alphaConsRecId :: TH.Name -> Id -> RewriteH CoreProg
alphaConsRecId n v =  setFailMsg (wrongFormForAlpha "ProgCons (Rec bs) p") $
                      do v' <- constT (cloneVarH (\ _ -> TH.nameBase n) v)
                         consRecDefT (\ _ -> replaceVarR v v')
                                     (replaceVarR v v')
                                     (\ bs e -> ProgCons (Rec $ (map.first) (replaceVar v v') bs) e)

-- | Rename the specified identifiers in a recursive top-level binding at the head of a program, using the suggested names where provided.
alphaConsRecIdsWith :: [(TH.Name,Id)] -> RewriteH CoreProg
alphaConsRecIdsWith = andR . map (uncurry alphaConsRecId)

-- | Rename the identifiers bound in the top-level binding at the head of the program with the given list of suggested names.
alphaConsWith :: [TH.Name] -> RewriteH CoreProg
alphaConsWith []     = fail "At least one new name must be provided."
alphaConsWith (n:ns) = alphaConsNonRec n <+ (consRecIdsT >>= (alphaConsRecIdsWith . zip (n:ns)))

-- -- | Rename the specified variables bound in the top-level binding at the head of the program.
-- alphaConsIds :: [Id] -> RewriteH CoreProg
-- alphaConsIds vs = alphaConsNonRecIds Nothing vs <+ alphaConsRecIdsWith (zip (repeat Nothing) vs)

-- -- | Rename all identifiers bound in the top-level binding at the head of the program.
-- alphaCons :: RewriteH CoreProg
-- alphaCons = consIdsT >>= alphaConsIds

-----------------------------------------------------------------------

-- -- | Rename all identifiers bound at the top-level.
-- alphaProg :: RewriteH CoreProg
-- alphaProg = progNilT ProgNil <+ (alphaCons >>> progConsAllR idR alphaProg)

-----------------------------------------------------------------------

-- | Alpha rename any bindings at this node.  Note: does not rename case alternatives unless invoked on the alternative.
alpha :: RewriteH Core
alpha = setFailMsg "Cannot alpha-rename here." $
           promoteExprR (alphaLam Nothing <+ alphaCaseBinder Nothing <+ alphaLet)
        <+ promoteAltR alphaAlt

-----------------------------------------------------------------------

wrongFormForAlpha :: String -> String
wrongFormForAlpha s = "Cannot alpha-rename, " ++ wrongExprForm s

-----------------------------------------------------------------------
