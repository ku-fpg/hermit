{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module HERMIT.Dictionary.Reasoning
    ( -- * Equational Reasoning
      externals
    , EqualityProof
    , flipEquality
    , eqLhsIntroR
    , eqRhsIntroR
    , birewrite
    , extensionalityR
    , getLemmasT
    , getLemmaByNameT
    , insertLemmaR
    , lemmaR
    , markLemmaUsedR
    , modifyLemmaR
    -- ** Lifting transformations over 'Equality'
    , lhsT
    , rhsT
    , bothT
    , forallVarsT
    , lhsR
    , rhsR
    , bothR
    , ppEqualityT
    , proveEqualityT
    , verifyEqualityT
    , verifyEqualityLeftToRightT
    , verifyEqualityCommonTargetT
    , verifyIsomorphismT
    , verifyRetractionT
    , retractionBR
    , alphaEqualityR
    , unshadowEqualityR
    , instantiateDictsR
    , instantiateEquality
    , instantiateEqualityVar
    , instantiateEqualityVarR
    , discardUniVars
    , rememberR
    , unfoldRememberedR
    , foldRememberedR
    , foldAnyRememberedR
    ) where

import           Control.Applicative
import           Control.Arrow
import           Control.Monad
import           Control.Monad.IO.Class

import qualified Data.Map as Map
import           Data.List (isPrefixOf, nubBy)
import           Data.Maybe (fromMaybe)
import           Data.Monoid

import           HERMIT.Context
import           HERMIT.Core
import           HERMIT.External
import           HERMIT.GHC hiding ((<>))
import           HERMIT.Kure
import           HERMIT.Monad
import           HERMIT.Name
import           HERMIT.ParserCore
import           HERMIT.ParserType
import           HERMIT.PrettyPrinter.Common
import           HERMIT.Utilities

import           HERMIT.Dictionary.AlphaConversion hiding (externals)
import           HERMIT.Dictionary.Common
import           HERMIT.Dictionary.Fold hiding (externals)
import           HERMIT.Dictionary.GHC hiding (externals)
import           HERMIT.Dictionary.Local.Let (nonRecIntroR)
import           HERMIT.Dictionary.Unfold hiding (externals)

import qualified Text.PrettyPrint.MarkedHughesPJ as PP

------------------------------------------------------------------------------

externals :: [External]
externals =
    [ external "retraction" ((\ f g r -> promoteExprBiR $ retraction (Just r) f g) :: CoreString -> CoreString -> RewriteH Core -> BiRewriteH Core)
        [ "Given f :: X -> Y and g :: Y -> X, and a proof that f (g y) ==> y, then"
        , "f (g y) <==> y."
        ] .+ Shallow
    , external "retraction-unsafe" ((\ f g -> promoteExprBiR $ retraction Nothing f g) :: CoreString -> CoreString -> BiRewriteH Core)
        [ "Given f :: X -> Y and g :: Y -> X, then"
        , "f (g y) <==> y."
        , "Note that the precondition (f (g y) == y) is expected to hold."
        ] .+ Shallow .+ PreCondition
    , external "alpha-equality" ((\ nm newName -> alphaEqualityR (cmpString2Var nm) (const newName)))
        [ "Alpha-rename a universally quantified variable." ]
    , external "unshadow-equality" unshadowEqualityR
        [ "Unshadow an equality." ]
    , external "lemma" (promoteExprBiR . lemmaR :: LemmaName -> BiRewriteH Core)
        [ "Generate a bi-directional rewrite from a lemma." ]
    , external "lemma-lhs-intro" (lemmaLhsIntroR :: LemmaName -> RewriteH Core)
        [ "Introduce the LHS of a lemma as a non-recursive binding, in either an expression or a program."
        , "body ==> let v = lhs in body" ] .+ Introduce .+ Shallow
    , external "lemma-rhs-intro" (lemmaRhsIntroR :: LemmaName -> RewriteH Core)
        [ "Introduce the RHS of a lemma as a non-recursive binding, in either an expression or a program."
        , "body ==> let v = rhs in body" ] .+ Introduce .+ Shallow
    , external "inst-lemma" (\ nm v cs -> modifyLemmaR nm id (instantiateEqualityVarR (cmpString2Var v) cs) id id :: RewriteH Core)
        [ "Instantiate one of the universally quantified variables of the given lemma,"
        , "with the given Core expression, creating a new lemma. Instantiating an"
        , "already proven lemma will result in the new lemma being considered proven." ]
    , external "inst-lemma-dictionaries" (\ nm -> modifyLemmaR nm id instantiateDictsR id id :: RewriteH Core)
        [ "Instantiate all of the universally quantified dictionaries of the given lemma."
        , "Only works on dictionaries whose types are monomorphic (no free type variables)." ]
    , external "copy-lemma" (\ nm newName -> modifyLemmaR nm (const newName) idR id id :: RewriteH Core)
        [ "Copy a given lemma, with a new name." ]
    , external "modify-lemma" (\ nm rr -> modifyLemmaR nm id rr (const False) (const False) :: RewriteH Core)
        [ "Modify a given lemma. Resets the proven status to Not Proven and used status to Not Used." ]
    , external "query-lemma" ((\ nm t -> getLemmaByNameT nm >>> arr lemmaEq >>> t) :: LemmaName -> TransformH Equality String -> TransformH Core String)
        [ "Apply a transformation to a lemma, returning the result." ]
    , external "extensionality" (extensionalityR . Just :: String -> RewriteH Equality)
        [ "Given a name 'x, then"
        , "f == g  ==>  forall x.  f x == g x" ]
    , external "extensionality" (extensionalityR Nothing :: RewriteH Equality)
        [ "f == g  ==>  forall x.  f x == g x" ]
    , external "lhs" (lhsR . extractR :: RewriteH Core -> RewriteH Equality)
        [ "Apply a rewrite to the LHS of an equality." ]
    , external "lhs" (lhsT . extractT :: TransformH CoreTC String -> TransformH Equality String)
        [ "Apply a transformation to the LHS of an equality." ]
    , external "rhs" (rhsR . extractR :: RewriteH Core -> RewriteH Equality)
        [ "Apply a rewrite to the RHS of an equality." ]
    , external "rhs" (rhsT . extractT :: TransformH CoreTC String -> TransformH Equality String)
        [ "Apply a transformation to the RHS of an equality." ]
    , external "both" (bothR . extractR :: RewriteH Core -> RewriteH Equality)
        [ "Apply a rewrite to both sides of an equality, succeeding if either succeed." ]
    , external "both" ((\t -> liftM (\(r,s) -> unlines [r,s]) (bothT (extractT t))) :: TransformH CoreTC String -> TransformH Equality String)
        [ "Apply a transformation to the RHS of an equality." ]
    , external "remember" (rememberR :: LemmaName -> RewriteH Core)
        [ "Remember the current binding, allowing it to be folded/unfolded in the future." ] .+ Context
    , external "unfold-remembered" (promoteExprR . unfoldRememberedR :: LemmaName -> RewriteH Core)
        [ "Unfold a remembered definition." ] .+ Deep .+ Context
    , external "fold-remembered" (promoteExprR . foldRememberedR :: LemmaName -> RewriteH Core)
        [ "Fold a remembered definition." ]                      .+ Context .+ Deep
    , external "fold-any-remembered" (promoteExprR foldAnyRememberedR :: RewriteH Core)
        [ "Attempt to fold any of the remembered definitions." ] .+ Context .+ Deep
    ]

------------------------------------------------------------------------------

type EqualityProof c m = (Rewrite c m CoreExpr, Rewrite c m CoreExpr)

-- | Flip the LHS and RHS of a 'Equality'.
flipEquality :: Equality -> Equality
flipEquality (Equality xs lhs rhs) = Equality xs rhs lhs

-- | f == g  ==>  forall x.  f x == g x
extensionalityR :: Maybe String -> Rewrite c HermitM Equality
extensionalityR mn = prefixFailMsg "extensionality failed: " $
  do Equality vs lhs rhs <- idR

     let tyL = exprKindOrType lhs
         tyR = exprKindOrType rhs
     guardMsg (tyL `typeAlphaEq` tyR) "type mismatch between sides of equality.  This shouldn't happen, so is probably a bug."

     -- TODO: use the fresh-name-generator in AlphaConversion to avoid shadowing.
     (_,argTy,_) <- splitFunTypeM tyL
     v <- constT $ newVarH (fromMaybe "x" mn) argTy

     let x = varToCoreExpr v

     return $ Equality (vs ++ [v]) (mkCoreApp lhs x) (mkCoreApp rhs x)

------------------------------------------------------------------------------

-- | @e@ ==> @let v = lhs in e@
eqLhsIntroR :: Equality -> Rewrite c HermitM Core
eqLhsIntroR (Equality bs lhs _) = nonRecIntroR "lhs" (mkCoreLams bs lhs)

-- | @e@ ==> @let v = rhs in e@
eqRhsIntroR :: Equality -> Rewrite c HermitM Core
eqRhsIntroR (Equality bs _ rhs) = nonRecIntroR "rhs" (mkCoreLams bs rhs)

------------------------------------------------------------------------------

-- | Create a 'BiRewrite' from a 'Equality'.
--
-- The high level idea: create a temporary function with two definitions.
-- Fold one of the defintions, then immediately unfold the other.
birewrite :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c
             , ReadPath c Crumb, MonadCatch m, MonadUnique m )
          => Equality -> BiRewrite c m CoreExpr
birewrite (Equality bnds l r) = bidirectional (foldUnfold l r) (foldUnfold r l)
    where foldUnfold lhs rhs = transform $ \ c e -> do
            let lhsLam = mkCoreLams bnds lhs
            -- we use a unique, transitory variable for the 'function' we are folding
            v <- newIdH "biTemp" (exprType lhsLam)
            e' <- maybe (fail "folding LHS failed") return (fold v lhsLam e)
            let rhsLam = mkCoreLams bnds rhs
                -- create a temporary context with an unfolding for the
                -- transitory function so we can reuse unfoldR.
                c' = addHermitBindings [(v, NONREC rhsLam, mempty)] c
            applyT unfoldR c' e'

-- | Lift a transformation over 'CoreExpr' into a transformation over the left-hand side of a 'Equality'.
lhsT :: (AddBindings c, Monad m, ReadPath c Crumb) => Transform c m CoreExpr b -> Transform c m Equality b
lhsT t = idR >>= \ (Equality vs lhs _) -> return lhs >>> withVarsInScope vs t

-- | Lift a transformation over 'CoreExpr' into a transformation over the right-hand side of a 'Equality'.
rhsT :: (AddBindings c, Monad m, ReadPath c Crumb) => Transform c m CoreExpr b -> Transform c m Equality b
rhsT t = idR >>= \ (Equality vs _ rhs) -> return rhs >>> withVarsInScope vs t

-- | Lift a transformation over 'CoreExpr' into a transformation over both sides of a 'Equality'.
bothT :: (AddBindings c, Monad m, ReadPath c Crumb) => Transform c m CoreExpr b -> Transform c m Equality (b,b)
bothT t = liftM2 (,) (lhsT t) (rhsT t) -- Can't wait for Applicative to be a superclass of Monad

-- | Lift a transformation over '[Var]' into a transformation over the universally quantified variables of a 'Equality'.
forallVarsT :: Monad m => Transform c m [Var] b -> Transform c m Equality b
forallVarsT t = idR >>= \ (Equality vs _ _) -> return vs >>> t

-- | Lift a rewrite over 'CoreExpr' into a rewrite over the left-hand side of a 'Equality'.
lhsR :: (AddBindings c, Monad m, ReadPath c Crumb) => Rewrite c m CoreExpr -> Rewrite c m Equality
lhsR r = do
    Equality vs lhs rhs <- idR
    lhs' <- withVarsInScope vs r <<< return lhs
    return $ Equality vs lhs' rhs

-- | Lift a rewrite over 'CoreExpr' into a rewrite over the right-hand side of a 'Equality'.
rhsR :: (AddBindings c, Monad m, ReadPath c Crumb) => Rewrite c m CoreExpr -> Rewrite c m Equality
rhsR r = do
    Equality vs lhs rhs <- idR
    rhs' <- withVarsInScope vs r <<< return rhs
    return $ Equality vs lhs rhs'

-- | Lift a rewrite over 'CoreExpr' into a rewrite over both sides of a 'Equality'.
bothR :: (AddBindings c, MonadCatch m, ReadPath c Crumb) => Rewrite c m CoreExpr -> Rewrite c m Equality
bothR r = lhsR r >+> rhsR r

------------------------------------------------------------------------------

ppEqualityT :: PrettyPrinter -> TransformH Equality DocH
ppEqualityT pp = do
    let pos = pOptions pp
    d1 <- forallVarsT (liftPrettyH pos $ pForall pp)
    (d2,d3) <- bothT (liftPrettyH pos $ extractT $ pCoreTC pp)
    return $ PP.sep [d1,d2,syntaxColor (PP.text "="),d3]

------------------------------------------------------------------------------

-- Idea: use Haskell's functions to fill the holes automagically
--
-- plusId <- findIdT "+"
-- timesId <- findIdT "*"
-- mkEquality $ \ x -> ( mkCoreApps (Var plusId)  [x,x]
--                     , mkCoreApps (Var timesId) [Lit 2, x])
--
-- TODO: need to know type of 'x' to generate a variable.
class BuildEquality a where
    mkEquality :: a -> HermitM Equality

instance BuildEquality (CoreExpr,CoreExpr) where
    mkEquality :: (CoreExpr,CoreExpr) -> HermitM Equality
    mkEquality (lhs,rhs) = return $ Equality [] lhs rhs

instance BuildEquality a => BuildEquality (CoreExpr -> a) where
    mkEquality :: (CoreExpr -> a) -> HermitM Equality
    mkEquality f = do
        x <- newIdH "x" (error "need to create a type")
        Equality bnds lhs rhs <- mkEquality (f (varToCoreExpr x))
        return $ Equality (x:bnds) lhs rhs

------------------------------------------------------------------------------

-- | Verify that a 'Equality' holds, by applying a rewrite to each side, and checking that the results are equal.
proveEqualityT :: forall c m. (AddBindings c, Monad m, ReadPath c Crumb)
                        => EqualityProof c m -> Transform c m Equality ()
proveEqualityT (l,r) = lhsR l >>> rhsR r >>> verifyEqualityT

-- | Verify that the left- and right-hand sides of a 'Equality' are alpha equivalent.
verifyEqualityT :: Monad m => Transform c m Equality ()
verifyEqualityT = do
    Equality _ lhs rhs <- idR
    guardMsg (exprAlphaEq lhs rhs) "the two sides of the equality do not match."

------------------------------------------------------------------------------

-- TODO: are these other functions used? If so, can they be rewritten in terms of lhsR and rhsR as above?

-- | Given two expressions, and a rewrite from the former to the latter, verify that rewrite.
verifyEqualityLeftToRightT :: MonadCatch m => CoreExpr -> CoreExpr -> Rewrite c m CoreExpr -> Transform c m a ()
verifyEqualityLeftToRightT sourceExpr targetExpr r =
  prefixFailMsg "equality verification failed: " $
  do resultExpr <- r <<< return sourceExpr
     guardMsg (exprAlphaEq targetExpr resultExpr) "result of running proof on lhs of equality does not match rhs of equality."

-- | Given two expressions, and a rewrite to apply to each, verify that the resulting expressions are equal.
verifyEqualityCommonTargetT :: MonadCatch m => CoreExpr -> CoreExpr -> EqualityProof c m -> Transform c m a ()
verifyEqualityCommonTargetT lhs rhs (l,r) =
  prefixFailMsg "equality verification failed: " $
  do lhsResult <- l <<< return lhs
     rhsResult <- r <<< return rhs
     guardMsg (exprAlphaEq lhsResult rhsResult) "results of running proofs on both sides of equality do not match."

------------------------------------------------------------------------------

-- Note: We use global Ids for verification to avoid out-of-scope errors.

-- | Given f :: X -> Y and g :: Y -> X, verify that f (g y) ==> y and g (f x) ==> x.
verifyIsomorphismT :: CoreExpr -> CoreExpr -> Rewrite c HermitM CoreExpr -> Rewrite c HermitM CoreExpr -> Transform c HermitM a ()
verifyIsomorphismT f g fgR gfR = prefixFailMsg "Isomorphism verification failed: " $
   do (tyX, tyY) <- funExprsWithInverseTypes f g
      x          <- constT (newGlobalIdH "x" tyX)
      y          <- constT (newGlobalIdH "y" tyY)
      verifyEqualityLeftToRightT (App f (App g (Var y))) (Var y) fgR
      verifyEqualityLeftToRightT (App g (App f (Var x))) (Var x) gfR

-- | Given f :: X -> Y and g :: Y -> X, verify that f (g y) ==> y.
verifyRetractionT :: CoreExpr -> CoreExpr -> Rewrite c HermitM CoreExpr -> Transform c HermitM a ()
verifyRetractionT f g r = prefixFailMsg "Retraction verification failed: " $
   do (_tyX, tyY) <- funExprsWithInverseTypes f g
      y           <- constT (newGlobalIdH "y" tyY)
      let lhs = App f (App g (Var y))
          rhs = Var y
      verifyEqualityLeftToRightT lhs rhs r

------------------------------------------------------------------------------

-- | Given f :: X -> Y and g :: Y -> X, and a proof that f (g y) ==> y, then f (g y) <==> y.
retractionBR :: forall c. Maybe (Rewrite c HermitM CoreExpr) -> CoreExpr -> CoreExpr -> BiRewrite c HermitM CoreExpr
retractionBR mr f g = beforeBiR
                         (prefixFailMsg "Retraction failed: " $
                          do whenJust (verifyRetractionT f g) mr
                             y        <- idR
                             (_, tyY) <- funExprsWithInverseTypes f g
                             guardMsg (exprKindOrType y `typeAlphaEq` tyY) "type of expression does not match given retraction components."
                             return y
                         )
                         (\ y -> bidirectional
                                   retractionL
                                   (return $ App f (App g y))
                         )
  where
    retractionL :: Rewrite c HermitM CoreExpr
    retractionL =  prefixFailMsg "Retraction failed: " $
                   withPatFailMsg (wrongExprForm "App f (App g y)") $
      do App f' (App g' y) <- idR
         guardMsg (exprAlphaEq f f' && exprAlphaEq g g') "given retraction components do not match current expression."
         return y

-- | Given @f :: X -> Y@ and @g :: Y -> X@, and a proof that @f (g y)@ ==> @y@, then @f (g y)@ <==> @y@.
retraction :: Maybe (RewriteH Core) -> CoreString -> CoreString -> BiRewriteH CoreExpr
retraction mr = parse2beforeBiR (retractionBR (extractR <$> mr))

------------------------------------------------------------------------------

-- TODO: revisit this for binder re-ordering issue
instantiateDictsR :: RewriteH Equality
instantiateDictsR = prefixFailMsg "Dictionary instantiation failed: " $ do
    bs <- forallVarsT idR
    let dArgs = filter (\b -> isId b && isDictTy (varType b)) bs
        uniqDs = nubBy (\ b1 b2 -> eqType (varType b1) (varType b2)) dArgs
    guardMsg (not (null uniqDs)) "no universally quantified dictionaries can be instantiated."
    ds <- forM uniqDs $ \ b -> constT $ do
            (i,bnds) <- buildDictionary b
            let dExpr = case bnds of
                            [NonRec v e] | i == v -> e -- the common case that we would have gotten a single non-recursive let
                            _ -> mkCoreLets bnds (varToCoreExpr i)
                new = varSetElems $ delVarSetList (localFreeVarsExpr dExpr) bs
            return (b,dExpr,new)
    let buildSubst :: Monad m => Var -> m (Var, CoreExpr, [Var])
        buildSubst b = case [ (b,e,[]) | (b',e,_) <- ds, eqType (varType b) (varType b') ] of
                        [] -> fail "cannot find equivalent dictionary expression (impossible!)"
                        [t] -> return t
                        _   -> fail "multiple dictionary expressions found (impossible!)"
        lookup3 :: Var -> [(Var,CoreExpr,[Var])] -> (Var,CoreExpr,[Var])
        lookup3 v l = head [ t | t@(v',_,_) <- l, v == v' ]
    allDs <- forM dArgs $ \ b -> constT $ do
                if b `elem` uniqDs
                then return $ lookup3 b ds
                else buildSubst b
    contextfreeT $ instantiateEquality allDs

------------------------------------------------------------------------------

alphaEqualityR :: (Var -> Bool) -> (String -> String) -> RewriteH Equality
alphaEqualityR p f = prefixFailMsg "Alpha-renaming binder in equality failed: " $ do
    Equality bs lhs rhs <- idR
    guardMsg (any p bs) "specified variable is not universally quantified."

    let (bs',i:vs) = break p bs -- this is safe because we know i is in bs
    i' <- constT $ cloneVarH f i

    let inS           = delVarSetList (unionVarSets (map localFreeVarsExpr [lhs, rhs] ++ map freeVarsVar vs)) (i:i':vs)
        subst         = extendSubst (mkEmptySubst (mkInScopeSet inS)) i (varToCoreExpr i')
        (subst', vs') = substBndrs subst vs
        lhs'          = substExpr (text "coreExprEquality-lhs") subst' lhs
        rhs'          = substExpr (text "coreExprEquality-rhs") subst' rhs
    return $ Equality (bs'++(i':vs')) lhs' rhs'

unshadowEqualityR :: RewriteH Equality
unshadowEqualityR = prefixFailMsg "Unshadowing equality failed: " $ do
    c@(Equality bs _ _) <- idR
    bvs <- boundVarsT
    let visible = unionVarSets [bvs , freeVarsEquality c]
    ss <- varSetElems <$> detectShadowsM bs visible
    guardMsg (not (null ss)) "no shadows to eliminate."
    let f = freshNameGenAvoiding Nothing . extendVarSet visible
    andR [ alphaEqualityR (==s) (f s) | s <- reverse ss ] >>> bothR (tryR unshadowExprR)

freeVarsEquality :: Equality -> VarSet
freeVarsEquality (Equality bs lhs rhs) =
    delVarSetList (unionVarSets (map freeVarsExpr [lhs,rhs])) bs

------------------------------------------------------------------------------

instantiateEqualityVarR :: (Var -> Bool) -> CoreString -> RewriteH Equality
instantiateEqualityVarR p cs = prefixFailMsg "instantiation failed: " $ do
    bs <- forallVarsT idR
    (e,new) <- case filter p bs of
                [] -> fail "no universally quantified variables match predicate."
                (b:_) | isId b    -> let (before,_) = break (==b) bs
                                     in liftM (,[]) $ withVarsInScope before $ parseCoreExprT cs
                      | otherwise -> do let (before,_) = break (==b) bs
                                        (ty, tvs) <- withVarsInScope before $ parseTypeWithHolesT cs
                                        return (Type ty, tvs)
    eq <- contextfreeT $ instantiateEqualityVar p e new
    (_,_) <- return eq >>> bothT lintExprT -- sanity check
    return eq

-- | Instantiate one of the universally quantified variables in a 'Equality'.
-- Note: assumes implicit ordering of variables, such that substitution happens to the right
-- as it does in case alternatives. Only first variable that matches predicate is
-- instantiated.
instantiateEqualityVar :: MonadIO m => (Var -> Bool) -- predicate to select var
                                    -> CoreExpr      -- expression to instantiate with
                                    -> [Var]         -- new binders to add in place of var
                                    -> Equality -> m Equality
instantiateEqualityVar p e new (Equality bs lhs rhs)
    | not (any p bs) = fail "specified variable is not universally quantified."
    | otherwise = do
        let (bs',i:vs) = break p bs -- this is safe because we know i is in bs
            tyVars    = filter isTyVar bs'
            failMsg   = fail "type of provided expression differs from selected binder."

            -- unifyTypes will give back mappings from a TyVar to itself
            -- we don't want to do these instantiations, or else variables
            -- become unbound
            dropSelfSubst :: [(TyVar, Type)] -> [(TyVar,Type)]
            dropSelfSubst ps = [ (v,t) | (v,t) <- ps, case t of
                                                        TyVarTy v' | v' == v -> False
                                                        _ -> True ]
        tvs <- maybe failMsg (return . tyMatchesToCoreExpr . dropSelfSubst)
                $ unifyTypes tyVars (varType i) (exprKindOrType e)

        let inS           = delVarSetList (unionVarSets (map localFreeVarsExpr [lhs, rhs, e] ++ map freeVarsVar vs)) (i:vs)
            subst         = extendSubst (mkEmptySubst (mkInScopeSet inS)) i e
            (subst', vs') = substBndrs subst vs
            lhs'          = substExpr (text "equality-lhs") subst' lhs
            rhs'          = substExpr (text "equality-rhs") subst' rhs
        instantiateEquality (noAdds tvs) $ Equality (bs'++new++vs') lhs' rhs'

noAdds :: [(Var,CoreExpr)] -> [(Var,CoreExpr,[Var])]
noAdds ps = [ (v,e,[]) | (v,e) <- ps ]

-- | Instantiate a set of universally quantified variables in a 'Equality'.
-- It is important that all type variables appear before any value-level variables in the first argument.
instantiateEquality :: MonadIO m => [(Var,CoreExpr,[Var])] -> Equality -> m Equality
instantiateEquality = flip (foldM (\ eq (v,e,vs) -> instantiateEqualityVar (==v) e vs eq)) . reverse
-- foldM is a left-to-right fold, so the reverse is important to do substitutions in reverse order
-- which is what we want (all value variables should be instantiated before type variables).

------------------------------------------------------------------------------

discardUniVars :: Equality -> Equality
discardUniVars (Equality _ lhs rhs) = Equality [] lhs rhs

------------------------------------------------------------------------------

getLemmasT :: HasLemmas m => Transform c m x Lemmas
getLemmasT = constT getLemmas

getLemmaByNameT :: (HasLemmas m, Monad m) => LemmaName -> Transform c m x Lemma
getLemmaByNameT nm = getLemmasT >>= maybe (fail $ "No lemma named: " ++ show nm) return . Map.lookup nm

lemmaR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
          , HasLemmas m, MonadCatch m, MonadUnique m)
       => LemmaName -> BiRewrite c m CoreExpr
lemmaR nm = afterBiR (beforeBiR (getLemmaByNameT nm) (birewrite . lemmaEq)) (markLemmaUsedR nm)

------------------------------------------------------------------------------

-- We use sideEffectR because only rewrites generate new state in the Kernel.

insertLemmaR :: (HasLemmas m, Monad m) => LemmaName -> Lemma -> Rewrite c m a
insertLemmaR nm l = sideEffectR $ \ _ _ -> insertLemma nm l

modifyLemmaR :: (HasLemmas m, Monad m)
             => LemmaName
             -> (LemmaName -> LemmaName) -- ^ modify lemma name
             -> Rewrite c m Equality     -- ^ rewrite the equality
             -> (Bool -> Bool)           -- ^ modify proven status
             -> (Bool -> Bool)           -- ^ modify used status
             -> Rewrite c m a
modifyLemmaR nm nFn rr pFn uFn = do
    Lemma eq p u <- getLemmaByNameT nm
    eq' <- rr <<< return eq
    sideEffectR $ \ _ _ -> insertLemma (nFn nm) $ Lemma eq' (pFn p) (uFn u)

markLemmaUsedR :: (HasLemmas m, Monad m) => LemmaName -> Rewrite c m a
markLemmaUsedR nm = modifyLemmaR nm id idR id (const True)

------------------------------------------------------------------------------

lemmaNameToEqualityT :: (HasLemmas m, Monad m) => LemmaName -> Transform c m x Equality
lemmaNameToEqualityT nm = liftM lemmaEq $ getLemmaByNameT nm

-- | @e@ ==> @let v = lhs in e@  (also works in a similar manner at Program nodes)
lemmaLhsIntroR :: LemmaName -> RewriteH Core
lemmaLhsIntroR = lemmaNameToEqualityT >=> eqLhsIntroR

-- | @e@ ==> @let v = rhs in e@  (also works in a similar manner at Program nodes)
lemmaRhsIntroR :: LemmaName -> RewriteH Core
lemmaRhsIntroR = lemmaNameToEqualityT >=> eqRhsIntroR

------------------------------------------------------------------------------

prefixRemembered :: LemmaName -> LemmaName
prefixRemembered = ("remembered-" <>)

-- | Remember a binding with a name for later use. Allows us to look at past definitions.
rememberR :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb) => LemmaName -> Rewrite c HermitM Core
rememberR nm = prefixFailMsg "remember failed: " $ do
    Def v e <- setFailMsg "not applied to a binding." $ defOrNonRecT idR idR Def
    insertLemmaR (prefixRemembered nm) $ Lemma (Equality [] (varToCoreExpr v) e) True False

-- | Unfold a remembered definition (like unfoldR, but looks in stash instead of context).
unfoldRememberedR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
                     , HasLemmas m, MonadCatch m, MonadUnique m)
                  => LemmaName -> Rewrite c m CoreExpr
unfoldRememberedR = prefixFailMsg "Unfolding remembered definition failed: " . forwardT . lemmaR . prefixRemembered

-- | Fold a remembered definition (like foldR, but looks in stash instead of context).
foldRememberedR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
                   , HasLemmas m, MonadCatch m, MonadUnique m)
                => LemmaName -> Rewrite c m CoreExpr
foldRememberedR = prefixFailMsg "Folding remembered definition failed: " . backwardT . lemmaR . prefixRemembered

-- | Fold any of the remembered definitions.
foldAnyRememberedR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
                      , HasLemmas m, MonadCatch m, MonadUnique m)
                   => Rewrite c m CoreExpr
foldAnyRememberedR = setFailMsg "Fold failed: no definitions could be folded." $ do
    nms <- liftM Map.keys getLemmasT
    catchesM [ backwardT (lemmaR nm) | nm <- nms, "remembered-" `isPrefixOf` show nm ]
