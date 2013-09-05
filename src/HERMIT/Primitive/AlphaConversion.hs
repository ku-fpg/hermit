{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}
module HERMIT.Primitive.AlphaConversion
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
       , alphaProgConsWith
         -- ** Shadow Detection and Unshadowing
       , unshadow
       , visibleVarsT
       , freshNameGenT
       , freshNameGenAvoiding
       , replaceVarR
       )
where

import Control.Applicative
import Control.Arrow
import Control.Monad (liftM, liftM2)
import Data.Char (isDigit)
import Data.List (intersect)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Monoid

import HERMIT.Core
import HERMIT.Context
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC

import HERMIT.Primitive.GHC hiding (externals)
import HERMIT.Primitive.Common

import qualified Language.Haskell.TH as TH

import Prelude hiding (exp)

-----------------------------------------------------------------------

-- | Externals for alpha-renaming.
externals :: [External]
externals = map (.+ Deep)
         [  external "alpha" (alpha :: RewriteH Core)
               [ "Renames the bound variables at the current node."]
         ,  external "alpha-lam" (promoteExprR . alphaLam . Just :: TH.Name -> RewriteH Core)
               [ "Renames the bound variable in a Lambda expression to the given name."]
         ,  external "alpha-lam" (promoteExprR  (alphaLam Nothing) :: RewriteH Core)
               [ "Renames the bound variable in a Lambda expression."]
         ,  external "alpha-case-binder" (promoteExprR . alphaCaseBinder . Just :: TH.Name -> RewriteH Core)
               [ "Renames the binder in a Case expression to the given name."]
         ,  external "alpha-case-binder" (promoteExprR (alphaCaseBinder Nothing) :: RewriteH Core)
               [ "Renames the binder in a Case expression."]
         ,  external "alpha-alt" (promoteAltR alphaAlt :: RewriteH Core)
               [ "Renames all binders in a Case alternative."]
         ,  external "alpha-alt" (promoteAltR . alphaAltWith :: [TH.Name] -> RewriteH Core)
               [ "Renames all binders in a Case alternative using the user-provided list of new names."]
         ,  external "alpha-case" (promoteExprR alphaCase :: RewriteH Core)
               [ "Renames all binders in a Case alternative."]
         ,  external "alpha-let" (promoteExprR . alphaLetWith :: [TH.Name] -> RewriteH Core)
               [ "Renames the bound variables in a Let expression using a list of suggested names."]
         ,  external "alpha-let" (promoteExprR alphaLet :: RewriteH Core)
               [ "Renames the bound variables in a Let expression."]
         ,  external "alpha-top" (promoteProgR . alphaProgConsWith :: [TH.Name] -> RewriteH Core)
               [ "Renames the bound identifiers in the top-level binding group at the head of the program using a list of suggested names."]
         -- ,  external "alpha-top" (promoteProgR alphaCons)
         --       [ "Renames the bound identifiers in the top-level binding at the head of the program."]
         -- ,  external "alpha-program" (promoteProgR alphaProg)
         --       [ "Renames identifiers bound at the top-level of the program."]
         ,  external "unshadow" (unshadow :: RewriteH Core)
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
visibleVarsT :: (BoundVars c, Monad m) => Translate c m CoreExpr VarSet
visibleVarsT = liftM2 unionVarSet boundVarsT (arr freeVarsExpr)

-- | If a name is provided replace the string with that,
--   otherwise modify the string making sure to /not/ clash with any visible variables.
freshNameGenT :: (BoundVars c, Monad m) => Maybe TH.Name -> Translate c m CoreExpr (String -> String)
freshNameGenT mn = freshNameGenAvoiding mn `liftM` visibleVarsT

-- | Use the optional argument if given, otherwise generate a new name avoiding clashes with the list of variables.
freshNameGenAvoiding :: Maybe TH.Name -> VarSet -> (String -> String)
freshNameGenAvoiding mn vs str = maybe (inventNames vs str) TH.nameBase mn

-- | Invent a new String based on the old one, but avoiding clashing with the given list of identifiers.
inventNames :: VarSet -> String -> String
inventNames curr old = head
                     [ nm
                     | nm <- old : [ base ++ show uq | uq <- [start ..] :: [Int] ]
                     , nm `notElem` names
                     ]
   where
           names = map uqName (varSetElems curr)
           nums = reverse $ takeWhile isDigit (reverse old)
           baseLeng = length $ drop (length nums) old
           base = take baseLeng old
           start = case reads nums of
                     [(v,_)] -> v + 1
                     _       -> 0


-- | Remove all variables from the first set that shadow a variable in the second set.
shadowedBy :: VarSet -> VarSet -> VarSet
shadowedBy vs fvs = let fvUqNames = map uqName (varSetElems fvs)
                     in filterVarSet (\ v -> uqName v `elem` fvUqNames) vs

-- | Lifted version of 'shadowedBy'.
--   Additionally, it fails if no shadows are found.
shadowedByT :: MonadCatch m => Translate c m a VarSet -> Translate c m a VarSet -> Translate c m a VarSet
shadowedByT t1 t2 = setFailMsg "No shadows detected." $ (liftM2 shadowedBy t1 t2) >>> acceptR (not . isEmptyVarSet)

-- | Rename local variables with manifestly unique names (x, x0, x1, ...).
--   Does not rename top-level definitions.
unshadow :: forall c. (ExtendPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM Core
unshadow = setFailMsg "No shadows to eliminate." $
           anytdR (promoteExprR unshadowExpr <+ promoteAltR unshadowAlt)

  where
    unshadowExpr :: Rewrite c HermitM CoreExpr
    unshadowExpr = do vs <- shadowedByT (mkVarSet <$> (letVarsT <+ (return <$> (caseWildIdT <+ lamVarT))))
                                        (unionVarSet <$> boundVarsT <*> arr freeVarsExpr)
                      alphaLam Nothing <+ alphaLetVars (varSetElems vs) <+ alphaCaseBinder Nothing

    unshadowAlt :: Rewrite c HermitM CoreAlt
    unshadowAlt = do vs <- shadowedByT (arr (mkVarSet . altVars))
                                       (unionVarSet <$> boundVarsT <*> arr freeVarsAlt)
                     alphaAltVars (varSetElems vs)

-----------------------------------------------------------------------

-- | Replace all occurrences of a specified variable.
--   Arguments are the variable to replace and the replacement variable, respectively.
replaceVarR :: (ExtendPath c Crumb, AddBindings c, Injection a Core, MonadCatch m) => Var -> Var -> Rewrite c m a
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
alphaLam :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => Maybe TH.Name -> Rewrite c HermitM CoreExpr
alphaLam mn = setFailMsg (wrongFormForAlpha "Lam v e") $
              do (v, nameModifier) <- lamT idR (freshNameGenT mn) (,)
                 v' <- constT (cloneVarH nameModifier v)
                 lamAnyR (arr $ replaceVar v v') (replaceVarR v v')

-----------------------------------------------------------------------

-- | Alpha rename a case binder.  Optionally takes a suggested new name.
alphaCaseBinder :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => Maybe TH.Name -> Rewrite c HermitM CoreExpr
alphaCaseBinder mn = setFailMsg (wrongFormForAlpha "Case e v ty alts") $
                     do Case _ v _ _ <- idR
                        nameModifier <- freshNameGenT mn
                        v' <- constT (cloneVarH nameModifier v)
                        caseAnyR idR (return v') idR (\ _ -> replaceVarR v v')

-----------------------------------------------------------------------

-- | Rename the specified variable in a case alternative.  Optionally takes a suggested new name.
alphaAltVar :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => Maybe TH.Name -> Var -> Rewrite c HermitM CoreAlt
alphaAltVar mn v = do nameModifier <- altT idR (\ _ -> idR) (freshNameGenT mn) (\ _ _ nameGen -> nameGen)
                      v' <- constT (cloneVarH nameModifier v)
                      altAnyR (fail "") (\ _ -> arr (replaceVar v v')) (replaceVarR v v')

-- | Rename the specified variables in a case alternative, using the suggested names where provided.
alphaAltVarsWith :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => [(Maybe TH.Name,Var)] -> Rewrite c HermitM CoreAlt
alphaAltVarsWith = andR . map (uncurry alphaAltVar)

-- | Rename the variables bound in a case alternative with the given list of suggested names.
alphaAltWith :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => [TH.Name] -> Rewrite c HermitM CoreAlt
alphaAltWith ns = do vs <- arr altVars
                     alphaAltVarsWith $ zip (map Just ns) vs

-- | Rename the specified variables in a case alternative.
alphaAltVars :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => [Var] -> Rewrite c HermitM CoreAlt
alphaAltVars vs = do bs <- arr altVars
                     alphaAltVarsWith (zip (repeat Nothing) (bs `intersect` vs))

-- | Rename all identifiers bound in a case alternative.
alphaAlt :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM CoreAlt
alphaAlt = arr altVars >>= alphaAltVars

-----------------------------------------------------------------------

-- | Rename all identifiers bound in a case expression.
alphaCase :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM CoreExpr
alphaCase = alphaCaseBinder Nothing >+> caseAllR idR idR idR (const alphaAlt)

-----------------------------------------------------------------------

-- | Alpha rename a non-recursive let binder.  Optionally takes a suggested new name.
alphaLetNonRec :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => Maybe TH.Name -> Rewrite c HermitM CoreExpr
alphaLetNonRec mn = setFailMsg (wrongFormForAlpha "Let (NonRec v e1) e2") $
                    do (v, nameModifier) <- letNonRecT idR mempty (freshNameGenT mn) (\ v () nameMod -> (v, nameMod))
                       v' <- constT (cloneVarH nameModifier v)
                       letNonRecAnyR (return v') idR (replaceVarR v v')

-- | Alpha rename a non-recursive let binder if the variable appears in the argument list.  Optionally takes a suggested new name.
alphaLetNonRecVars :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => Maybe TH.Name -> [Var] -> Rewrite c HermitM CoreExpr
alphaLetNonRecVars mn vs = whenM ((`elem` vs) <$> letNonRecVarT) (alphaLetNonRec mn)

-- | Rename the specified identifier bound in a recursive let.  Optionally takes a suggested new name.
alphaLetRecId :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => Maybe TH.Name -> Id -> Rewrite c HermitM CoreExpr
alphaLetRecId mn v = setFailMsg (wrongFormForAlpha "Let (Rec bs) e") $
                     do usedVars <- unionVarSet <$> boundVarsT
                                                <*> letRecT (\ _ -> defT idR (arr freeVarsExpr) (flip extendVarSet)) (arr freeVarsExpr) (\ bndfvs vs -> unionVarSets (vs:bndfvs))
                        v' <- constT (cloneVarH (freshNameGenAvoiding mn usedVars) v)
                        letRecDefAnyR (\ _ -> (arr (replaceVar v v'), replaceVarR v v')) (replaceVarR v v')

-- | Rename the specified identifiers in a recursive let, using the suggested names where provided.
alphaLetRecIdsWith :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => [(Maybe TH.Name,Id)] -> Rewrite c HermitM CoreExpr
alphaLetRecIdsWith = andR . map (uncurry alphaLetRecId)

-- | Rename the identifiers bound in a Let with the given list of suggested names.
alphaLetWith :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => [TH.Name] -> Rewrite c HermitM CoreExpr
alphaLetWith ns = alphaLetNonRec (listToMaybe ns)
                  <+ (letRecIdsT >>= (alphaLetRecIdsWith . zip (map Just ns)))

-- | Rename the specified variables bound in a let.
alphaLetVars :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => [Var] -> Rewrite c HermitM CoreExpr
alphaLetVars vs = alphaLetNonRecVars Nothing vs <+ (do bs <- letT (arr bindVars) successT const
                                                       alphaLetRecIdsWith (zip (repeat Nothing) (bs `intersect` vs))
                                                   )

-- | Rename all identifiers bound in a Let.
alphaLet :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM CoreExpr
alphaLet = letVarsT >>= alphaLetVars

-----------------------------------------------------------------------

-- | Alpha rename a non-recursive top-level binder.  Optionally takes a suggested new name.
alphaProgConsNonRec :: (ExtendPath c Crumb, AddBindings c) => TH.Name -> Rewrite c HermitM CoreProg
alphaProgConsNonRec n = setFailMsg (wrongFormForAlpha "ProgCons (NonRec v e) p") $
                    do ProgCons (NonRec v _) _ <- idR
                       v' <- constT (cloneVarH (\ _ -> TH.nameBase n) v)
                       consNonRecAnyR (return v') idR (replaceVarR v v')

-- -- | Alpha rename a non-recursive top-level binder if the identifier appears in the argument list.  Optionally takes a suggested new name.
-- alphaConsNonRecIds :: Maybe TH.Name -> [Id] -> Rewrite c m CoreProg
-- alphaConsNonRecIds mn vs = whenM ((`elem` vs) <$> consNonRecIdT) (alphaConsNonRec mn)

-- | Rename the specified identifier bound in a recursive top-level binder.  Optionally takes a suggested new name.
alphaProgConsRecId :: (ExtendPath c Crumb, AddBindings c) => TH.Name -> Id -> Rewrite c HermitM CoreProg
alphaProgConsRecId n v =  setFailMsg (wrongFormForAlpha "ProgCons (Rec bs) p") $
                      do v' <- constT (cloneVarH (\ _ -> TH.nameBase n) v)
                         consRecDefAnyR (\ _ -> (arr (replaceVar v v'), replaceVarR v v')) (replaceVarR v v')

-- | Rename the specified identifiers in a recursive top-level binding at the head of a program, using the suggested names where provided.
alphaProgConsRecIdsWith :: (ExtendPath c Crumb, AddBindings c) => [(TH.Name,Id)] -> Rewrite c HermitM CoreProg
alphaProgConsRecIdsWith = andR . map (uncurry alphaProgConsRecId)

-- | Rename the identifiers bound in the top-level binding at the head of the program with the given list of suggested names.
alphaProgConsWith :: (ExtendPath c Crumb, AddBindings c) => [TH.Name] -> Rewrite c HermitM CoreProg
alphaProgConsWith []     = fail "At least one new name must be provided."
alphaProgConsWith (n:ns) = alphaProgConsNonRec n <+ (progConsRecIdsT >>= (alphaProgConsRecIdsWith . zip (n:ns)))

-- -- | Rename the specified variables bound in the top-level binding at the head of the program.
-- alphaConsIds :: [Id] -> Rewrite c m CoreProg
-- alphaConsIds vs = alphaConsNonRecIds Nothing vs <+ alphaConsRecIdsWith (zip (repeat Nothing) vs)

-- -- | Rename all identifiers bound in the top-level binding at the head of the program.
-- alphaCons :: Rewrite c m CoreProg
-- alphaCons = consIdsT >>= alphaConsIds

-----------------------------------------------------------------------

-- -- | Rename all identifiers bound at the top-level.
-- alphaProg :: Rewrite c m CoreProg
-- alphaProg = progNilT ProgNil <+ (alphaCons >>> progConsAllR idR alphaProg)

-----------------------------------------------------------------------

-- | Alpha rename any bindings at this node.  Note: does not rename case alternatives unless invoked on the alternative.
alpha :: (ExtendPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM Core
alpha = setFailMsg "Cannot alpha-rename here." $
           promoteExprR (alphaLam Nothing <+ alphaCaseBinder Nothing <+ alphaLet)
        <+ promoteAltR alphaAlt

-----------------------------------------------------------------------

wrongFormForAlpha :: String -> String
wrongFormForAlpha s = "Cannot alpha-rename, " ++ wrongExprForm s

-----------------------------------------------------------------------
