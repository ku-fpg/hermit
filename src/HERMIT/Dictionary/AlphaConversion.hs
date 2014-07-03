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
       , alphaProgConsIdsR
       , alphaProgConsR
       , alphaProgR
         -- ** Shadow Detection and Unshadowing
       , unshadowR
       , unshadowExprR
       , unshadowAltR
       , unshadowProgR
       , visibleVarsT
       , cloneVarAvoidingT
--       , freshNameGenAvoidingT
       , freshNameGenAvoiding
       , detectShadowsM
       , replaceVarR
       )
where

import Control.Applicative
import Control.Arrow
import Control.Monad (liftM2)
import Data.Char (isDigit)
import Data.Function (on)
import Data.List (intersect, delete, elemIndex)
import Data.Maybe (listToMaybe)

import HERMIT.Core
import HERMIT.Context
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC
import HERMIT.Name
import HERMIT.Utilities(dupsBy)

import HERMIT.Dictionary.GHC hiding (externals)
import HERMIT.Dictionary.Common

import Prelude hiding (exp)

-----------------------------------------------------------------------

-- | Externals for alpha-renaming.
externals :: [External]
externals = map (.+ Deep)
         [  external "alpha" (alphaR :: RewriteH Core)
               [ "Renames the bound variables at the current node."]
         ,  external "alpha-lam" (promoteExprR . alphaLamR . Just :: String -> RewriteH Core)
               [ "Renames the bound variable in a Lambda expression to the given name."]
         ,  external "alpha-lam" (promoteExprR  (alphaLamR Nothing) :: RewriteH Core)
               [ "Renames the bound variable in a Lambda expression."]
         ,  external "alpha-case-binder" (promoteExprR . alphaCaseBinderR . Just :: String -> RewriteH Core)
               [ "Renames the binder in a Case expression to the given name."]
         ,  external "alpha-case-binder" (promoteExprR (alphaCaseBinderR Nothing) :: RewriteH Core)
               [ "Renames the binder in a Case expression."]
         ,  external "alpha-alt" (promoteAltR alphaAltR :: RewriteH Core)
               [ "Renames all binders in a Case alternative."]
         ,  external "alpha-alt" (promoteAltR . alphaAltWithR :: [String] -> RewriteH Core)
               [ "Renames all binders in a Case alternative using the user-provided list of new names."]
         ,  external "alpha-case" (promoteExprR alphaCaseR :: RewriteH Core)
               [ "Renames all binders in a Case alternative."]
         ,  external "alpha-let" (promoteExprR . alphaLetWithR :: [String] -> RewriteH Core)
               [ "Renames the bound variables in a Let expression using a list of suggested names."]
         ,  external "alpha-let" (promoteExprR alphaLetR :: RewriteH Core)
               [ "Renames the bound variables in a Let expression."]
         ,  external "alpha-top" (promoteProgR . alphaProgConsWithR :: [String] -> RewriteH Core)
               [ "Renames the bound identifiers in the top-level binding group at the head of the program using a list of suggested names."]
         ,  external "alpha-top" (promoteProgR alphaProgConsR :: RewriteH Core)
               [ "Renames the bound identifiers in the top-level binding at the head of the program."]
         ,  external "alpha-prog" (promoteProgR alphaProgR :: RewriteH Core)
               [ "Rename all top-level identifiers in the program."]
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

-- | Collect all visible variables (in the expression or the context).
visibleVarsT :: (BoundVars c, Monad m) => Transform c m CoreTC VarSet
visibleVarsT = liftM2 unionVarSet boundVarsT (arr freeVarsCoreTC)

-- | If a name is provided, use that as the name of the new variable.
--   Otherwise modify the variable name making sure to /not/ clash with the given variables or any visible variables.
cloneVarAvoidingT :: BoundVars c => Var -> Maybe String -> [Var] -> Transform c HermitM CoreTC Var
cloneVarAvoidingT v mn vs =
  do vvs <- visibleVarsT
     let nameModifier = freshNameGenAvoiding mn (extendVarSetList vvs vs)
     constT (cloneVarH nameModifier v)

-- | Use the optional argument if given, otherwise generate a new name avoiding clashes with the set of variables.
freshNameGenAvoiding :: Maybe String -> VarSet -> (String -> String)
freshNameGenAvoiding mn vs str = maybe (inventNames vs str) ((\(c:cs) -> reverse (c:(takeWhile (/='.') cs))) . reverse) mn
-- The 'Just' case above gives the unqualified portion of the name (properly handling the compose operator '.')

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


-- | Discard variables from the first set that do not shadow a variable in the second set.
shadowedBy :: VarSet -> VarSet -> VarSet
shadowedBy vs fvs = let fvUqNames = map uqName (varSetElems fvs)
                     in filterVarSet (\ v -> uqName v `elem` fvUqNames) vs

-- | Shadows are any duplicates in the list, or any occurrences of the list elements in the set.
detectShadowsM :: Monad m => [Var] -> VarSet -> m VarSet
detectShadowsM bs fvs = let ss = shadowedBy (mkVarSet bs) fvs `extendVarSetList` dupVars bs
                         in do guardMsg (not $ isEmptyVarSet ss) "No shadows detected."
                               return ss

-- | Rename local variables with manifestly unique names (x, x0, x1, ...).
--   Does not rename top-level definitions.
unshadowR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, HasEmptyContext c, ReadPath c Crumb)
          => Rewrite c HermitM Core
unshadowR = setFailMsg "No shadows to eliminate." $
    anytdR (promoteExprR unshadowExprR <+ promoteAltR unshadowAltR <+ promoteProgR unshadowProgR)

unshadowExprR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, ReadPath c Crumb)
              => Rewrite c HermitM CoreExpr
unshadowExprR = do
    bs  <- letVarsT <+ (return <$> (caseBinderIdT <+ lamVarT))
    fvs <- unionVarSet <$> boundVarsT <*> arr freeVarsExpr
    ss  <- detectShadowsM bs fvs
    alphaLamR Nothing <+ alphaLetVarsR (varSetElems ss) <+ alphaCaseBinderR Nothing

unshadowAltR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, ReadPath c Crumb)
             => Rewrite c HermitM CoreAlt
unshadowAltR = do
    bs  <- arr altVars
    fvs <- unionVarSet <$> boundVarsT <*> arr freeVarsAlt
    ss  <- detectShadowsM bs fvs
    alphaAltVarsR (varSetElems ss)

unshadowProgR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, ReadPath c Crumb)
              => Rewrite c HermitM CoreProg
unshadowProgR = do
    bs  <- progConsIdsT
    fvs <- unionVarSet <$> boundVarsT <*> arr freeVarsProg
    ss  <- detectShadowsM bs fvs
    alphaProgConsIdsR (varSetElems ss)

dupVars :: [Var] -> [Var]
dupVars = dupsBy ((==) `on` uqName)

-----------------------------------------------------------------------

-- Maybe this should be defined in Dictionary.GHC.

-- | Replace all occurrences of a specified variable.
--   Arguments are the variable to replace and the replacement variable, respectively.
replaceVarR :: (Injection a Core, MonadCatch m) => Var -> Var -> Rewrite c m a
replaceVarR v v' = extractR $ tryR $ substR v $ varToCoreExpr v'

-- TODO: Experimental
replaceRecBindVarR :: Monad m => Id -> Id -> Rewrite c m CoreBind
replaceRecBindVarR v v' =
   do Rec ies <- idR
      let (is,es) = unzip ies
      case elemIndex v is of
        Nothing -> fail "Specified identifier does not occur in the current recursive binding group."
        Just n  -> let is0       = delete v is
                       (is1,is2) = splitAt n is0
                       is'       = is1 ++ v' : is2
                       es'       = map (substCoreExpr v (Var v')) es
                       -- TODO.  Do we need to initialize the emptySubst with bindFreeVars?
                       sub       = extendSubst emptySubst v (Var v')
                   in return $ snd $ substBind sub (Rec (zip is' es'))

                   -- let is0       = delete v is
                   --     emptySub  = mkEmptySubst $ mkInScopeSet $ unionVarSets (map (localFreeVarsExpr . Var) is0)
                   --     sub       = extendSubst emptySub v (Var v')
                   --     (is1,is2) = splitAt n (snd $ substRecBndrs sub is0)
                   --     is'       = is1 ++ v' : is2
                   --     es'       = map (substCoreExpr v (Var v')) es
                   -- in return $ Rec (zip is' es')

-----------------------------------------------------------------------

-- | Alpha rename a lambda binder.  Optionally takes a suggested new name.
alphaLamR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe String -> Rewrite c HermitM CoreExpr
alphaLamR mn = setFailMsg (wrongFormForAlpha "Lam v e") $
              do v  <- lamVarT
                 v' <- extractT (cloneVarAvoidingT v mn [v])
                 lamAnyR (return v') (replaceVarR v v')

-----------------------------------------------------------------------

-- | Alpha rename a case binder.  Optionally takes a suggested new name.
alphaCaseBinderR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe String -> Rewrite c HermitM CoreExpr
alphaCaseBinderR mn = setFailMsg (wrongFormForAlpha "Case e i ty alts") $
                     do i  <- caseBinderIdT
                        i' <- extractT (cloneVarAvoidingT i mn [i])
                        caseAnyR idR (return i') idR (\ _ -> replaceVarR i i')

-----------------------------------------------------------------------

-- | Rename the specified variable in a case alternative.  Optionally takes a suggested new name.
alphaAltVarR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe String -> Var -> Rewrite c HermitM CoreAlt
alphaAltVarR mn v = do
    (con, vs, rhs) <- idR
    v' <- extractT (cloneVarAvoidingT v mn vs)

    -- This is a bit of a hack. We include all the binders *after* v in the call to substAltR,
    -- then put the binders before v, and v', back on the front. The use of substAltR this way,
    -- handles the case where v is a type binder which substitutes into the types of bs'.
    -- It's a hack because we depend on substAltR not noticing that the constructor is not applied
    -- to enough binders.
    case break (==v) vs of
        (bs,_:bs') -> let (con',bs'',rhs') = substCoreAlt v (varToCoreExpr v') (con,bs',rhs)
                       in return (con',bs ++ (v':bs''),rhs')
        _ -> fail "pattern binder not present."

-- | Rename the specified variables in a case alternative, using the suggested names where provided.
-- Suggested names *must* be provided in left-to-right order matching the order of the alt binders.
alphaAltVarsWithR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [(Maybe String,Var)] -> Rewrite c HermitM CoreAlt
alphaAltVarsWithR = andR . map (uncurry alphaAltVarR) . reverse -- note: right-to-left so type subst aren't undone

-- | Rename the variables bound in a case alternative with the given list of suggested names.
alphaAltWithR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [String] -> Rewrite c HermitM CoreAlt
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
alphaLetNonRecR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe String -> Rewrite c HermitM CoreExpr
alphaLetNonRecR mn = setFailMsg (wrongFormForAlpha "Let (NonRec v e1) e2") $
                    do v  <- letNonRecVarT
                       v' <- extractT (cloneVarAvoidingT v mn [v])
                       letNonRecAnyR (return v') idR (replaceVarR v v')

-- | Alpha rename a non-recursive let binder if the variable appears in the argument list.  Optionally takes a suggested new name.
alphaLetNonRecVarsR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe String -> [Var] -> Rewrite c HermitM CoreExpr
alphaLetNonRecVarsR mn vs = whenM ((`elem` vs) <$> letNonRecVarT) (alphaLetNonRecR mn)


-- TODO: Maybe it would be more efficient to rename all the Ids at once, rather than one by one?

-- | Rename the specified identifiers in a recursive let, using the suggested names where provided.
alphaLetRecIdsWithR :: forall c. (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [(Maybe String,Id)] -> Rewrite c HermitM CoreExpr
alphaLetRecIdsWithR = andR . map (uncurry alphaLetRecIdR)
  where
    -- | Rename the specified identifier bound in a recursive let.  Optionally takes a suggested new name.
    alphaLetRecIdR :: Maybe String -> Id -> Rewrite c HermitM CoreExpr
    alphaLetRecIdR mn i = setFailMsg (wrongFormForAlpha "Let (Rec bs) e") $
                     do is <- letRecIdsT
                        i' <- extractT (cloneVarAvoidingT i mn is)
                        letAnyR (replaceRecBindVarR i i') (replaceVarR i i')


-- | Rename the identifiers bound in a Let with the given list of suggested names.
alphaLetWithR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [String] -> Rewrite c HermitM CoreExpr
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
alphaProgConsNonRecR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe String -> Rewrite c HermitM CoreProg
alphaProgConsNonRecR mn = setFailMsg (wrongFormForAlpha "ProgCons (NonRec v e) p") $
                    do i <- progConsNonRecIdT
                       guardMsg (not $ isExportedId i) ("Identifier " ++ var2String i ++ " is exported, and thus cannot be alpha-renamed.")
                       i' <- extractT (cloneVarAvoidingT i mn [i])
                       consNonRecAnyR (return i') idR (replaceVarR i i')

-- | Alpha rename a non-recursive top-level binder if the identifier appears in the argument list.  Optionally takes a suggested new name.
alphaProgConsNonRecIdsR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Maybe String -> [Id] -> Rewrite c HermitM CoreProg
alphaProgConsNonRecIdsR mn is = whenM ((`elem` is) <$> progConsNonRecIdT) (alphaProgConsNonRecR mn)

-- TODO: Maybe it would be more efficient to rename all the Ids at once, rather than one by one?

-- | Rename the specified identifiers in a recursive top-level binding at the head of a program, using the suggested names where provided.
alphaProgConsRecIdsWithR :: forall c. (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [(Maybe String,Id)] -> Rewrite c HermitM CoreProg
alphaProgConsRecIdsWithR = andR . map (uncurry alphaProgConsRecIdR) . filter (not . isExportedId . snd)
  where
    -- | Rename the specified identifier bound in a recursive top-level binder.  Optionally takes a suggested new name.
    alphaProgConsRecIdR :: Maybe String -> Id -> Rewrite c HermitM CoreProg
    alphaProgConsRecIdR mn i =  setFailMsg (wrongFormForAlpha "ProgCons (Rec bs) p") $
                      do is <- progConsRecIdsT
                         i' <- extractT (cloneVarAvoidingT i mn is)
                         progConsAnyR (replaceRecBindVarR i i') (replaceVarR i i')


-- | Rename the identifiers bound in the top-level binding at the head of the program with the given list of suggested names.
alphaProgConsWithR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [String] -> Rewrite c HermitM CoreProg
alphaProgConsWithR ns = alphaProgConsNonRecR (listToMaybe ns)
                        <+ (progConsRecIdsT >>= (alphaProgConsRecIdsWithR . zip (map Just ns)))

-- | Rename the specified variables bound in the top-level binding at the head of the program.
alphaProgConsIdsR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => [Id] -> Rewrite c HermitM CoreProg
alphaProgConsIdsR vs = alphaProgConsNonRecIdsR Nothing vs
                       <+ (do bs <- progConsT (arr bindVars) successT const
                              alphaProgConsRecIdsWithR (zip (repeat Nothing) (bs `intersect` vs))
                          )

-- | Rename all identifiers bound in the top-level binding at the head of the program.
alphaProgConsR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM CoreProg
alphaProgConsR = progConsIdsT >>= alphaProgConsIdsR

-----------------------------------------------------------------------

-- | Rename all identifiers bound at the top-level.
alphaProgR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM CoreProg
alphaProgR = alphaProgConsR >+> progConsAllR idR alphaProgR

-----------------------------------------------------------------------

-- | Alpha rename any bindings at this node.  Note: does not rename case alternatives unless invoked on the alternative.
alphaR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c) => Rewrite c HermitM Core
alphaR = setFailMsg "Cannot alpha-rename here." $
           promoteExprR (alphaLamR Nothing <+ alphaCaseBinderR Nothing <+ alphaLetR)
        <+ promoteAltR alphaAltR
        <+ promoteProgR alphaProgConsR

-- TODO: Alpha rewrites need better error messages.  Currently the use of (<+) leads to incorrect error reporting.
--       Though really, we first need to improve KURE to have a version of (<+) that maintains the existing error message in the case of non-matching constructors henceforth.

-- TODO 2: Also, we should be able to rename inside types and coercions.

-----------------------------------------------------------------------

wrongFormForAlpha :: String -> String
wrongFormForAlpha s = "Cannot alpha-rename, " ++ wrongExprForm s

-----------------------------------------------------------------------
