{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}
module HERMIT.Dictionary.AlphaConversion
       ( -- * Alpha-Renaming and Shadowing
         externals
         -- ** Alpha-Renaming
       , alphaR
       , alphaLamR
       , alphaCaseBinderR
       , alphaAltWithR
       , alphaAltVarsR
       , alphaAltR
       , alphaCaseR
       , alphaLetWithR
       , alphaLetVarsR
       , alphaLetR
       , alphaProgConsWithR
         -- ** Shadow Detection and Unshadowing
       , unshadowR
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

import HERMIT.Dictionary.GHC hiding (externals)
import HERMIT.Dictionary.Common

import qualified Language.Haskell.TH as TH

import Prelude hiding (exp)

-----------------------------------------------------------------------

-- | Externals for alpha-renaming.
externals :: [External]
externals = map (.+ Deep)
         [  external "alpha" (alphaR :: RewriteH Core)
               [ "Renames the bound variables at the current node."]
         ,  external "alpha-lam" (promoteExprR . alphaLamR . Just :: TH.Name -> RewriteH Core)
               [ "Renames the bound variable in a Lambda expression to the given name."]
         ,  external "alpha-lam" (promoteExprR  (alphaLamR Nothing) :: RewriteH Core)
               [ "Renames the bound variable in a Lambda expression."]
         ,  external "alpha-case-binder" (promoteExprR . alphaCaseBinderR . Just :: TH.Name -> RewriteH Core)
               [ "Renames the binder in a Case expression to the given name."]
         ,  external "alpha-case-binder" (promoteExprR (alphaCaseBinderR Nothing) :: RewriteH Core)
               [ "Renames the binder in a Case expression."]
         ,  external "alpha-alt" (promoteAltR alphaAltR :: RewriteH Core)
               [ "Renames all binders in a Case alternative."]
         ,  external "alpha-alt" (promoteAltR . alphaAltWithR :: [TH.Name] -> RewriteH Core)
               [ "Renames all binders in a Case alternative using the user-provided list of new names."]
         ,  external "alpha-case" (promoteExprR alphaCaseR :: RewriteH Core)
               [ "Renames all binders in a Case alternative."]
         ,  external "alpha-let" (promoteExprR . alphaLetWithR :: [TH.Name] -> RewriteH Core)
               [ "Renames the bound variables in a Let expression using a list of suggested names."]
         ,  external "alpha-let" (promoteExprR alphaLetR :: RewriteH Core)
               [ "Renames the bound variables in a Let expression."]
         ,  external "alpha-top" (promoteProgR . alphaProgConsWithR :: [TH.Name] -> RewriteH Core)
               [ "Renames the bound identifiers in the top-level binding group at the head of the program using a list of suggested names."]
         -- ,  external "alpha-top" (promoteProgR alphaCons)
         --       [ "Renames the bound identifiers in the top-level binding at the head of the program."]
         -- ,  external "alpha-program" (promoteProgR alphaProg)
         --       [ "Renames identifiers bound at the top-level of the program."]
         ,  external "unshadow" (unshadowR :: RewriteH Core)
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
unshadowR :: forall c. (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM Core
unshadowR = setFailMsg "No shadows to eliminate." $
           anytdR (promoteExprR unshadowExpr <+ promoteAltR unshadowAlt)

  where
    unshadowExpr :: Rewrite c HermitM CoreExpr
    unshadowExpr = do vs <- shadowedByT (mkVarSet <$> (letVarsT <+ (return <$> (caseWildIdT <+ lamVarT))))
                                        (unionVarSet <$> boundVarsT <*> arr freeVarsExpr)
                      alphaLamR Nothing <+ alphaLetVarsR (varSetElems vs) <+ alphaCaseBinderR Nothing

    unshadowAlt :: Rewrite c HermitM CoreAlt
    unshadowAlt = do vs <- shadowedByT (arr (mkVarSet . altVars))
                                       (unionVarSet <$> boundVarsT <*> arr freeVarsAlt)
                     alphaAltVarsR (varSetElems vs)

-----------------------------------------------------------------------

-- Maybe this should be defined elsewhere.

-- | Replace all occurrences of a specified variable.
--   Arguments are the variable to replace and the replacement variable, respectively.
replaceVarR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Injection a Core, MonadCatch m) => Var -> Var -> Rewrite c m a
replaceVarR v v' = extractR $ tryR $ substR v $ varToCoreExpr v'

-- | Given a variable to replace, and a replacement, produce a 'Var' @->@ 'Var' function that
--   acts as an identity for all 'Var's except the one to replace, for which it returns the replacment.
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
alphaLamR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe TH.Name -> Rewrite c HermitM CoreExpr
alphaLamR mn = setFailMsg (wrongFormForAlpha "Lam v e") $
              do (v, nameModifier) <- lamT idR (freshNameGenT mn) (,)
                 v' <- constT (cloneVarH nameModifier v)
                 lamAnyR (arr $ replaceVar v v') (replaceVarR v v')

-----------------------------------------------------------------------

-- | Alpha rename a case binder.  Optionally takes a suggested new name.
alphaCaseBinderR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe TH.Name -> Rewrite c HermitM CoreExpr
alphaCaseBinderR mn = setFailMsg (wrongFormForAlpha "Case e v ty alts") $
                     do Case _ v _ _ <- idR
                        nameModifier <- freshNameGenT mn
                        v' <- constT (cloneVarH nameModifier v)
                        caseAnyR idR (return v') idR (\ _ -> replaceVarR v v')

-----------------------------------------------------------------------

-- | Rename the specified variable in a case alternative.  Optionally takes a suggested new name.
alphaAltVarR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe TH.Name -> Var -> Rewrite c HermitM CoreAlt
alphaAltVarR mn v =
  do nameModifier <- altT idR (\ _ -> idR) (freshNameGenT mn) (\ _ _ nameGen -> nameGen)
     v' <- constT (cloneVarH nameModifier v)
     altAnyR (fail "") (\ _ -> arr (replaceVar v v')) (replaceVarR v v')

-- | Rename the specified variables in a case alternative, using the suggested names where provided.
alphaAltVarsWithR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [(Maybe TH.Name,Var)] -> Rewrite c HermitM CoreAlt
alphaAltVarsWithR = andR . map (uncurry alphaAltVarR)

-- | Rename the variables bound in a case alternative with the given list of suggested names.
alphaAltWithR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [TH.Name] -> Rewrite c HermitM CoreAlt
alphaAltWithR ns =
  do vs <- arr altVars
     alphaAltVarsWithR $ zip (map Just ns) vs

-- | Rename the specified variables in a case alternative.
alphaAltVarsR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [Var] -> Rewrite c HermitM CoreAlt
alphaAltVarsR vs =
  do bs <- arr altVars
     alphaAltVarsWithR (zip (repeat Nothing) (bs `intersect` vs))

-- | Rename all identifiers bound in a case alternative.
alphaAltR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM CoreAlt
alphaAltR = arr altVars >>= alphaAltVarsR

-----------------------------------------------------------------------

-- | Rename all identifiers bound in a case expression.
alphaCaseR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM CoreExpr
alphaCaseR = alphaCaseBinderR Nothing >+> caseAllR idR idR idR (const alphaAltR)

-----------------------------------------------------------------------

-- | Alpha rename a non-recursive let binder.  Optionally takes a suggested new name.
alphaLetNonRecR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe TH.Name -> Rewrite c HermitM CoreExpr
alphaLetNonRecR mn = setFailMsg (wrongFormForAlpha "Let (NonRec v e1) e2") $
                    do (v, nameModifier) <- letNonRecT idR mempty (freshNameGenT mn) (\ v () nameMod -> (v, nameMod))
                       v' <- constT (cloneVarH nameModifier v)
                       letNonRecAnyR (return v') idR (replaceVarR v v')

-- | Alpha rename a non-recursive let binder if the variable appears in the argument list.  Optionally takes a suggested new name.
alphaLetNonRecVarsR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe TH.Name -> [Var] -> Rewrite c HermitM CoreExpr
alphaLetNonRecVarsR mn vs = whenM ((`elem` vs) <$> letNonRecVarT) (alphaLetNonRecR mn)

-- | Rename the specified identifier bound in a recursive let.  Optionally takes a suggested new name.
alphaLetRecIdR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe TH.Name -> Id -> Rewrite c HermitM CoreExpr
alphaLetRecIdR mn v = setFailMsg (wrongFormForAlpha "Let (Rec bs) e") $
                     do usedVars <- unionVarSet <$> boundVarsT
                                                <*> letRecT (\ _ -> defT idR (arr freeVarsExpr) (flip extendVarSet)) (arr freeVarsExpr) (\ bndfvs vs -> unionVarSets (vs:bndfvs))
                        v' <- constT (cloneVarH (freshNameGenAvoiding mn usedVars) v)
                        letRecDefAnyR (\ _ -> (arr (replaceVar v v'), replaceVarR v v')) (replaceVarR v v')

-- | Rename the specified identifiers in a recursive let, using the suggested names where provided.
alphaLetRecIdsWithR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [(Maybe TH.Name,Id)] -> Rewrite c HermitM CoreExpr
alphaLetRecIdsWithR = andR . map (uncurry alphaLetRecIdR)

-- | Rename the identifiers bound in a Let with the given list of suggested names.
alphaLetWithR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [TH.Name] -> Rewrite c HermitM CoreExpr
alphaLetWithR ns = alphaLetNonRecR (listToMaybe ns)
                  <+ (letRecIdsT >>= (alphaLetRecIdsWithR . zip (map Just ns)))

-- | Rename the specified variables bound in a let.
alphaLetVarsR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [Var] -> Rewrite c HermitM CoreExpr
alphaLetVarsR vs = alphaLetNonRecVarsR Nothing vs
                   <+ (do bs <- letT (arr bindVars) successT const
                          alphaLetRecIdsWithR (zip (repeat Nothing) (bs `intersect` vs))
                      )

-- | Rename all identifiers bound in a Let.
alphaLetR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM CoreExpr
alphaLetR = letVarsT >>= alphaLetVarsR

-----------------------------------------------------------------------

-- | Alpha rename a non-recursive top-level binder.  Optionally takes a suggested new name.
alphaProgConsNonRecR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c) => TH.Name -> Rewrite c HermitM CoreProg
alphaProgConsNonRecR n = setFailMsg (wrongFormForAlpha "ProgCons (NonRec v e) p") $
                    do ProgCons (NonRec v _) _ <- idR
                       v' <- constT (cloneVarH (\ _ -> TH.nameBase n) v)
                       consNonRecAnyR (return v') idR (replaceVarR v v')

-- -- | Alpha rename a non-recursive top-level binder if the identifier appears in the argument list.  Optionally takes a suggested new name.
-- alphaConsNonRecIds :: Maybe TH.Name -> [Id] -> Rewrite c m CoreProg
-- alphaConsNonRecIds mn vs = whenM ((`elem` vs) <$> consNonRecIdT) (alphaConsNonRec mn)

-- | Rename the specified identifier bound in a recursive top-level binder.  Optionally takes a suggested new name.
alphaProgConsRecIdR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c) => TH.Name -> Id -> Rewrite c HermitM CoreProg
alphaProgConsRecIdR n v =  setFailMsg (wrongFormForAlpha "ProgCons (Rec bs) p") $
                      do v' <- constT (cloneVarH (\ _ -> TH.nameBase n) v)
                         consRecDefAnyR (\ _ -> (arr (replaceVar v v'), replaceVarR v v')) (replaceVarR v v')

-- | Rename the specified identifiers in a recursive top-level binding at the head of a program, using the suggested names where provided.
alphaProgConsRecIdsWithR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c) => [(TH.Name,Id)] -> Rewrite c HermitM CoreProg
alphaProgConsRecIdsWithR = andR . map (uncurry alphaProgConsRecIdR)

-- | Rename the identifiers bound in the top-level binding at the head of the program with the given list of suggested names.
alphaProgConsWithR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c) => [TH.Name] -> Rewrite c HermitM CoreProg
alphaProgConsWithR []     = fail "At least one new name must be provided."
alphaProgConsWithR (n:ns) = alphaProgConsNonRecR n <+ (progConsRecIdsT >>= (alphaProgConsRecIdsWithR . zip (n:ns)))

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
alphaR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM Core
alphaR = setFailMsg "Cannot alpha-rename here." $
           promoteExprR (alphaLamR Nothing <+ alphaCaseBinderR Nothing <+ alphaLetR)
        <+ promoteAltR alphaAltR

-----------------------------------------------------------------------

wrongFormForAlpha :: String -> String
wrongFormForAlpha s = "Cannot alpha-rename, " ++ wrongExprForm s

-----------------------------------------------------------------------
