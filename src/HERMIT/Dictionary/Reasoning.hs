{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module HERMIT.Dictionary.Reasoning
    ( -- * Equational Reasoning
      externals
    , EqualityProof
    , eqLhsIntroR
    , eqRhsIntroR
    , birewrite
    , extensionalityR
    , getLemmasT
    , getLemmaByNameT
    , insertLemmaT
    , insertLemmasT
    , lemmaBiR
    , lemmaConsequentR
    , markLemmaUsedT
    , markLemmaProvenT
    , modifyLemmaT
    , showLemmaT
    , showLemmasT
    , ppLemmaT
    , ppClauseT
    , ppLCoreTCT
    , retraction
    , mergeQuantifiersR
    , conjunctLemmasT
    , disjunctLemmasT
    , implyLemmasT
    , lemmaConsequentBiR
    , lemmaLhsIntroR
    , lemmaRhsIntroR
    , splitAntecedentR
      -- ** Lifting transformations over 'Clause'
    , lhsT
    , rhsT
    , bothT
    , lhsR
    , rhsR
    , bothR
    , verifyClauseT
    , lemmaR
    , quantIdentitiesR
    , verifyOrCreateT
    , verifyEqualityLeftToRightT
    , verifyEqualityCommonTargetT
    , verifyIsomorphismT
    , verifyRetractionT
    , reflexivityR
    , simplifyClauseR
    , retractionBR
    , unshadowClauseR
    , instantiateDictsR
    , instantiateClauseVarR
    , abstractClauseR
    , csInQBodyT
      -- * Constructing Composite Lemmas
    , ($$)
    , ($$$)
    , (==>)
    , (-->)
    , (===)
    , (/\)
    , (\/)
    , ToCoreExpr(..)
    , newLemma
    ) where

import           Control.Arrow hiding ((<+>))
import           Control.Monad.Compat

import           Data.Either (partitionEithers)
import           Data.List (isInfixOf, nubBy)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Monoid
import           Data.Typeable (Typeable)

import           HERMIT.Context
import           HERMIT.Core
import           HERMIT.External
import           HERMIT.GHC hiding ((<>), (<+>), nest, ($+$), ($$))
import           HERMIT.Kure
import           HERMIT.Lemma
import           HERMIT.Monad
import           HERMIT.Name
import           HERMIT.ParserCore
import           HERMIT.ParserType
import           HERMIT.PrettyPrinter.Common
import           HERMIT.Utilities

import           HERMIT.Dictionary.Common
import           HERMIT.Dictionary.Fold hiding (externals)
import           HERMIT.Dictionary.Function hiding (externals)
import           HERMIT.Dictionary.GHC hiding (externals)
import           HERMIT.Dictionary.Local.Let (nonRecIntroR)

import           Prelude.Compat hiding ((<$>), (<*>))

import qualified Text.PrettyPrint.MarkedHughesPJ as PP

------------------------------------------------------------------------------

externals :: [External]
externals =
    [ external "retraction" ((\ f g r -> promoteExprBiR $ retraction (Just r) f g) :: CoreString -> CoreString -> RewriteH LCore -> BiRewriteH LCore)
        [ "Given f :: X -> Y and g :: Y -> X, and a proof that f (g y) ==> y, then"
        , "f (g y) <==> y."
        ] .+ Shallow
    , external "retraction-unsafe" ((\ f g -> promoteExprBiR $ retraction Nothing f g) :: CoreString -> CoreString -> BiRewriteH LCore)
        [ "Given f :: X -> Y and g :: Y -> X, then"
        , "f (g y) <==> y."
        , "Note that the precondition (f (g y) == y) is expected to hold."
        ] .+ Shallow .+ PreCondition
    , external "unshadow-quantified" (promoteClauseR unshadowClauseR :: RewriteH LCoreTC)
        [ "Unshadow a quantified clause." ]
    , external "merge-quantifiers" (\n1 n2 -> promoteR (mergeQuantifiersR (cmpHN2Var n1) (cmpHN2Var n2)) :: RewriteH LCore)
        [ "Merge quantifiers from two clauses if they have the same type."
        , "Example:"
        , "(forall (x::Int). foo x = x) ^ (forall (y::Int). bar y y = 5)"
        , "merge-quantifiers 'x 'y"
        , "forall (x::Int). (foo x = x) ^ (bar x x = 5)"
        , "Note: if only one quantifier matches, it will be floated if possible." ]
    , external "float-left" (\n1 -> promoteR (mergeQuantifiersR (cmpHN2Var n1) (const False)) :: RewriteH LCore)
        [ "Float quantifier out of left-hand side." ]
    , external "float-right" (\n1 -> promoteR (mergeQuantifiersR (const False) (cmpHN2Var n1)) :: RewriteH LCore)
        [ "Float quantifier out of right-hand side." ]
    , external "conjunct" (\n1 n2 n3 -> conjunctLemmasT n1 n2 n3 :: TransformH LCore ())
        [ "conjunct new-name lhs-name rhs-name" ]
    , external "disjunct" (\n1 n2 n3 -> disjunctLemmasT n1 n2 n3 :: TransformH LCore ())
        [ "disjunct new-name lhs-name rhs-name" ]
    , external "imply" (\n1 n2 n3 -> implyLemmasT n1 n2 n3 :: TransformH LCore ())
        [ "imply new-name antecedent-name consequent-name" ]
    , external "lemma-birewrite" (promoteExprBiR . lemmaBiR Obligation :: LemmaName -> BiRewriteH LCore)
        [ "Generate a bi-directional rewrite from a lemma." ]
    , external "lemma-forward" (forwardT . promoteExprBiR . lemmaBiR Obligation :: LemmaName -> RewriteH LCore)
        [ "Generate a rewrite from a lemma, left-to-right." ]
    , external "lemma-backward" (backwardT . promoteExprBiR . lemmaBiR Obligation :: LemmaName -> RewriteH LCore)
        [ "Generate a rewrite from a lemma, right-to-left." ]
    , external "lemma-consequent" (promoteClauseR . lemmaConsequentR Obligation :: LemmaName -> RewriteH LCore)
        [ "Match the current lemma with the consequent of an implication lemma."
        , "Upon success, replaces with antecedent of the implication, properly instantiated." ]
    , external "lemma-consequent-birewrite" (promoteExprBiR . lemmaConsequentBiR Obligation :: LemmaName -> BiRewriteH LCore)
        [ "Generate a bi-directional rewrite from the consequent of an implication lemma."
        , "The antecedent is instantiated and introduced as an unproven obligation." ]
    , external "lemma-lhs-intro" (promoteCoreR . lemmaLhsIntroR :: LemmaName -> RewriteH LCore)
        [ "Introduce the LHS of a lemma as a non-recursive binding, in either an expression or a program."
        , "body ==> let v = lhs in body" ] .+ Introduce .+ Shallow
    , external "lemma-rhs-intro" (promoteCoreR . lemmaRhsIntroR :: LemmaName -> RewriteH LCore)
        [ "Introduce the RHS of a lemma as a non-recursive binding, in either an expression or a program."
        , "body ==> let v = rhs in body" ] .+ Introduce .+ Shallow
    , external "inst-lemma" (\ nm v cs -> modifyLemmaT nm id (instantiateClauseVarR (cmpHN2Var v) cs) id id :: TransformH LCore ())
        [ "Instantiate one of the universally quantified variables of the given lemma,"
        , "with the given Core expression, creating a new lemma. Instantiating an"
        , "already proven lemma will result in the new lemma being considered proven." ]
    , external "inst-dictionaries" (promoteClauseR instantiateDictsR :: RewriteH LCore)
        [ "Instantiate all of the universally quantified dictionaries of the given lemma." ]
    , external "abstract-forall" ((\nm -> promoteClauseR . abstractClauseR nm . csInQBodyT) :: String -> CoreString -> RewriteH LCore)
        [ "Weaken a lemma by abstracting an expression to a new quantifier." ]
    , external "abstract-forall" ((\nm rr -> promoteClauseR $ abstractClauseR nm $ extractT rr >>> setFailMsg "path must focus on an expression" projectT) :: String -> RewriteH LCore -> RewriteH LCore)
        [ "Weaken a lemma by abstracting an expression to a new quantifier." ]
    , external "copy-lemma" (\ nm newName -> modifyLemmaT nm (const newName) idR id id :: TransformH LCore ())
        [ "Copy a given lemma, with a new name." ]
    , external "modify-lemma" ((\ nm rr -> modifyLemmaT nm id (extractR rr) (const NotProven) (const NotUsed)) :: LemmaName -> RewriteH LCore -> TransformH LCore ())
        [ "Modify a given lemma. Resets proven status to Not Proven and used status to Not Used." ]
    , external "query-lemma" ((\ nm t -> getLemmaByNameT nm >>> arr lemmaC >>> extractT t) :: LemmaName -> TransformH LCore String -> TransformH LCore String)
        [ "Apply a transformation to a lemma, returning the result." ]
    , external "show-lemma" ((\pp n -> showLemmaT n pp) :: PrettyPrinter -> LemmaName -> PrettyH LCore)
        [ "Display a lemma." ]
    , external "show-lemmas" ((\pp n -> showLemmasT (Just n) pp) :: PrettyPrinter -> LemmaName -> PrettyH LCore)
        [ "List lemmas whose names match search string." ]
    , external "show-lemmas" (showLemmasT Nothing :: PrettyPrinter -> PrettyH LCore)
        [ "List lemmas." ]
    , external "extensionality" (promoteR . extensionalityR . Just :: String -> RewriteH LCore)
        [ "Given a name 'x, then"
        , "f == g  ==>  forall x.  f x == g x" ]
    , external "extensionality" (promoteR (extensionalityR Nothing) :: RewriteH LCore)
        [ "f == g  ==>  forall x.  f x == g x" ]
    , external "lhs" (promoteClauseT . lhsT :: TransformH LCore String -> TransformH LCore String)
        [ "Apply a transformation to the LHS of a quantified clause." ]
    , external "lhs" (promoteClauseR . lhsR :: RewriteH LCore -> RewriteH LCore)
        [ "Apply a rewrite to the LHS of a quantified clause." ]
    , external "rhs" (promoteClauseT . rhsT :: TransformH LCore String -> TransformH LCore String)
        [ "Apply a transformation to the RHS of a quantified clause." ]
    , external "rhs" (promoteClauseR . rhsR :: RewriteH LCore -> RewriteH LCore)
        [ "Apply a rewrite to the RHS of a quantified clause." ]
    , external "both" (promoteClauseR . bothR :: RewriteH LCore -> RewriteH LCore)
        [ "Apply a rewrite to both sides of an equality, succeeding if either succeed." ]
    , external "both" ((\t -> do (r,s) <- promoteClauseT (bothT t); return (unlines [r,s])) :: TransformH LCore String -> TransformH LCore String)
        [ "Apply a transformation to both sides of a quantified clause." ]
    , external "reflexivity" (promoteClauseR (forallR idR reflexivityR <+ reflexivityR) :: RewriteH LCore)
        [ "Rewrite alpha-equivalence to true." ]
    , external "simplify-lemma" (simplifyClauseR :: RewriteH LCore)
        [ "Reduce a proof by applying reflexivity and logical operator identities." ]
    , external "split-antecedent" (promoteClauseR splitAntecedentR :: RewriteH LCore)
        [ "Split an implication of the form (q1 ^ q2) => q3 into q1 => (q2 => q3)" ]
    , external "lemma" (promoteClauseR . lemmaR Obligation :: LemmaName -> RewriteH LCore)
        [ "Rewrite clause to true using given lemma." ]
    , external "lemma-unsafe" (promoteClauseR . lemmaR UnsafeUsed :: LemmaName -> RewriteH LCore)
        [ "Rewrite clause to true using given lemma." ] .+ Unsafe
    ]

------------------------------------------------------------------------------

type EqualityProof c m = (Rewrite c m CoreExpr, Rewrite c m CoreExpr)

-- | f == g  ==>  forall x.  f x == g x
extensionalityR :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb) => Maybe String -> Rewrite c HermitM Clause
extensionalityR mn = prefixFailMsg "extensionality failed: " $
  do (vs,(lhs,rhs)) <- forallT idR (equivT idR idR (,)) (,) <+ equivT idR idR (\l r -> ([],(l,r)))

     let tyL = exprKindOrType lhs
         tyR = exprKindOrType rhs
     guardMsg (tyL `typeAlphaEq` tyR) "type mismatch between sides of equality.  This shouldn't happen, so is probably a bug."

     -- TODO: use the fresh-name-generator in AlphaConversion to avoid shadowing.
     (_,argTy,_) <- splitFunTypeM tyL
     v <- constT $ newVarH (fromMaybe "x" mn) argTy

     let x = varToCoreExpr v

     return $ Forall (vs ++ [v]) $ Equiv (mkCoreApp lhs x) (mkCoreApp rhs x)

------------------------------------------------------------------------------

-- | @e@ ==> @let v = lhs in e@
eqLhsIntroR :: Clause -> Rewrite c HermitM Core
eqLhsIntroR (Forall bs (Equiv lhs _)) = nonRecIntroR "lhs" (mkCoreLams bs lhs)
eqLhsIntroR _                         = fail "compound lemmas not supported."

-- | @e@ ==> @let v = rhs in e@
eqRhsIntroR :: Clause -> Rewrite c HermitM Core
eqRhsIntroR (Forall bs (Equiv _ rhs)) = nonRecIntroR "rhs" (mkCoreLams bs rhs)
eqRhsIntroR _                         = fail "compound lemmas not supported."

------------------------------------------------------------------------------

-- | Create a 'BiRewrite' from a 'Clause'.
birewrite :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c
             , ReadPath c Crumb, MonadCatch m, MonadUnique m )
          => Clause -> BiRewrite c m CoreExpr
birewrite cl = bidirectional (foldUnfold "left" id) (foldUnfold "right" flipEquality)
    where foldUnfold side f = transform $ \ c ->
                                maybeM ("expression did not match "++side++"-hand side")
                                . fold (map f (toEqualities cl)) c

------------------------------------------------------------------------------
-- TODO: deprecate these?
-- Yes, but later.  They're in the paper now.
-- We should be using "childR crumb", really.

-- | Lift a transformation over 'LCoreTC' into a transformation over the left-hand side of a 'Clause'.
lhsT :: (AddBindings c, HasEmptyContext c, LemmaContext c, ReadPath c Crumb, ExtendPath c Crumb, MonadCatch m)
     => Transform c m LCore a -> Transform c m Clause a
lhsT t = extractT $ catchesT [ f (childT cr t) | cr <- [Conj_Lhs, Disj_Lhs, Impl_Lhs, Eq_Lhs]
                                               , f <- [childT Forall_Body, id] ]

-- | Lift a transformation over 'LCoreTC' into a transformation over the right-hand side of a 'Clause'.
rhsT :: (AddBindings c, HasEmptyContext c, LemmaContext c, ReadPath c Crumb, ExtendPath c Crumb, MonadCatch m)
     => Transform c m LCore a -> Transform c m Clause a
rhsT t = extractT $ catchesT [ f (childT cr t) | cr <- [Conj_Rhs, Disj_Rhs, Impl_Rhs, Eq_Rhs]
                                               , f <- [childT Forall_Body, id] ]

-- | Lift a transformation over 'LCoreTC' into a transformation over both sides of a 'Clause'.
bothT :: (AddBindings c, HasEmptyContext c, LemmaContext c, ReadPath c Crumb, ExtendPath c Crumb, MonadCatch m)
      => Transform c m LCore a -> Transform c m Clause (a, a)
bothT t = (,) <$> lhsT t <*> rhsT t

-- | Lift a rewrite over 'LCoreTC' into a rewrite over the left-hand side of a 'Clause'.
lhsR :: (AddBindings c, HasEmptyContext c, LemmaContext c, ReadPath c Crumb, ExtendPath c Crumb, MonadCatch m)
     => Rewrite c m LCore -> Rewrite c m Clause
lhsR r = extractR $ catchesT [ f (childR cr r) | cr <- [Conj_Lhs, Disj_Lhs, Impl_Lhs, Eq_Lhs]
                                               , f <- [childR Forall_Body, id] ]

-- | Lift a rewrite over 'LCoreTC' into a rewrite over the right-hand side of a 'Clause'.
rhsR :: (AddBindings c, HasEmptyContext c, LemmaContext c, ReadPath c Crumb, ExtendPath c Crumb, MonadCatch m)
     => Rewrite c m LCore -> Rewrite c m Clause
rhsR r = extractR $ catchesT [ f (childR cr r) | cr <- [Conj_Rhs, Disj_Rhs, Impl_Rhs, Eq_Rhs]
                                               , f <- [childR Forall_Body, id] ]

-- | Lift a rewrite over 'LCoreTC' into a rewrite over both sides of a 'Clause'.
bothR :: (AddBindings c, HasEmptyContext c, LemmaContext c, ReadPath c Crumb, ExtendPath c Crumb, MonadCatch m)
      => Rewrite c m LCore -> Rewrite c m Clause
bothR r = lhsR r >+> rhsR r

------------------------------------------------------------------------------

showLemmasT :: Maybe LemmaName -> PrettyPrinter -> PrettyH a
showLemmasT mnm pp = do
    ls <- getLemmasT
    let ls' = Map.toList $ Map.filterWithKey (maybe (\ _ _ -> True) (\ nm n _ -> show nm `isInfixOf` show n) mnm) ls
    ds <- forM ls' $ \(nm,l) -> return l >>> ppLemmaT pp nm
    return $ PP.vcat ds

showLemmaT :: LemmaName -> PrettyPrinter -> PrettyH a
showLemmaT nm pp = getLemmaByNameT nm >>> ppLemmaT pp nm

ppLemmaT :: PrettyPrinter -> LemmaName -> PrettyH Lemma
ppLemmaT pp nm = do
    Lemma q p _u <- idR
    qDoc <- return q >>> ppClauseT pp
    let hDoc = PP.text (show nm) PP.<+> PP.text ("(" ++ show p ++ ")")
    return $ hDoc PP.$+$ PP.nest 2 qDoc

ppLCoreTCT :: PrettyPrinter -> PrettyH LCoreTC
ppLCoreTCT pp = promoteT (ppClauseT pp) <+ promoteT (pCoreTC pp)

ppClauseT :: PrettyPrinter -> PrettyH Clause
ppClauseT pp = do
    p <- absPathT
    let parenify = ppClauseT pp >>^ \ d -> syntaxColor (PP.text "(") PP.<> d PP.<> syntaxColor (PP.text ")")
    (forallT (pForall pp) (ppClauseT pp) (\ d1 d2 -> PP.sep [d1,d2])
        <+ conjT parenify parenify (\ d1 d2 -> PP.sep [d1,syntaxColor (specialSymbol p ConjSymbol),d2])
        <+ disjT parenify parenify (\ d1 d2 -> PP.sep [d1,syntaxColor (specialSymbol p DisjSymbol),d2])
        <+ implT parenify parenify (\ _nm d1 d2 -> PP.sep [d1,syntaxColor (specialSymbol p ImplSymbol),d2])
        <+ equivT (extractT $ pCoreTC pp) (extractT $ pCoreTC pp) (\ d1 d2 -> PP.sep [d1,specialSymbol p EquivSymbol,d2])
        <+ return (syntaxColor $ PP.text "true"))

------------------------------------------------------------------------------

verifyClauseT :: (AddBindings c, ReadPath c Crumb, ExtendPath c Crumb, MonadCatch m) => Transform c m Clause ()
verifyClauseT = setFailMsg "verification failed: clause must be true (perhaps try reflexivity first)" $ do
    CTrue <- idR
    return ()

lemmaR :: (LemmaContext c, HasLemmas m, MonadCatch m) => Used -> LemmaName -> Rewrite c m Clause
lemmaR used nm = prefixFailMsg "verification failed: " $ do
    Lemma cl _ _ <- getLemmaByNameT nm
    eq <- arr (cl `proves`)
    guardMsg eq "lemmas are not equivalent."
    markLemmaUsedT nm used
    return CTrue

verifyOrCreateT :: ( AddBindings c, ExtendPath c Crumb, HasCoreRules c, LemmaContext c, ReadBindings c, ReadPath c Crumb
                   , HasHermitMEnv m, HasLemmas m, LiftCoreM m, MonadCatch m )
                => Used -> LemmaName -> Clause -> Transform c m a ()
verifyOrCreateT u nm cl = do
    exists <- testM $ getLemmaByNameT nm
    if exists
    then return cl >>> lemmaR u nm >>> verifyClauseT
    else contextonlyT $ \ c -> sendKEnvMessage $ AddObligation (toHermitC c) nm $ Lemma cl NotProven u

reflexivityR :: Monad m => Rewrite c m Clause
reflexivityR = do
    Equiv lhs rhs <- idR
    guardMsg (exprAlphaEq lhs rhs) "the two sides are not alpha-equivalent."
    return CTrue

simplifyClauseR :: (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadPath c Crumb, MonadCatch m)
                => Rewrite c m LCore
simplifyClauseR = anybuR (promoteR quantIdentitiesR <+ promoteR reflexivityR)

quantIdentitiesR :: MonadCatch m => Rewrite c m Clause
quantIdentitiesR =
    trueConjLR <+ trueConjRR <+
    trueDisjLR <+ trueDisjRR <+
    trueImpliesR <+ impliesTrueR <+
    aImpliesAR <+ forallTrueR

trueConjLR :: Monad m => Rewrite c m Clause
trueConjLR = do
    Conj CTrue cl <- idR
    return cl

trueConjRR :: Monad m => Rewrite c m Clause
trueConjRR = do
    Conj cl CTrue <- idR
    return cl

trueDisjLR :: Monad m => Rewrite c m Clause
trueDisjLR = do
    Disj CTrue _ <- idR
    return CTrue

trueDisjRR :: Monad m => Rewrite c m Clause
trueDisjRR = do
    Disj _ CTrue <- idR
    return CTrue

trueImpliesR :: Monad m => Rewrite c m Clause
trueImpliesR = do
    Impl _ CTrue cl <- idR
    return cl

impliesTrueR :: Monad m => Rewrite c m Clause
impliesTrueR = do
    Impl _ _ CTrue <- idR
    return CTrue

forallTrueR :: Monad m => Rewrite c m Clause
forallTrueR = do
    Forall _ CTrue <- idR
    return CTrue

aImpliesAR :: Monad m => Rewrite c m Clause
aImpliesAR = do
    Impl _ a c <- idR
    guardMsg (a `proves` c) "antecedent does not prove consequent."
    return CTrue

splitAntecedentR :: MonadCatch m => Rewrite c m Clause
splitAntecedentR = prefixFailMsg "antecedent split failed: " $
                   withPatFailMsg (wrongExprForm "(ante1 ^ ante2) => con") $ do
    Impl nm (Conj c1 c2) con <- idR
    return $ Impl (nm <> "0") c1 $ Impl (nm <> "1") c2 con

------------------------------------------------------------------------------

-- TODO: everything between here and instantiateDictsR needs to be rethought/removed

-- TODO: this is used in century plugin, but otherwise should be removed

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
retraction :: Maybe (RewriteH LCore) -> CoreString -> CoreString -> BiRewriteH CoreExpr
retraction mr = parse2beforeBiR (retractionBR (extractR <$> mr))

------------------------------------------------------------------------------

-- TODO: revisit this for binder re-ordering issue
instantiateDictsR :: RewriteH Clause
instantiateDictsR = prefixFailMsg "Dictionary instantiation failed: " $ do
    bs <- forallT idR successT const
    let dArgs = filter (\b -> isId b && isDictTy (varType b)) bs
        uniqDs = nubBy (\ b1 b2 -> eqType (varType b1) (varType b2)) dArgs
    guardMsg (not (null uniqDs)) "no universally quantified dictionaries can be instantiated."
    ds <- forM uniqDs $ \ b -> constT $ do
            (i,bnds) <- buildDictionary b
            let dExpr = case bnds of
                            -- the common case that we would have gotten a single non-recursive let
                            [NonRec v e] | i == v -> e
                            _ -> mkCoreLets bnds (varToCoreExpr i)
            return (b,dExpr)
    let buildSubst :: Monad m => Var -> m (Var, CoreExpr)
        buildSubst b = case [ (b,e) | (b',e) <- ds, eqType (varType b) (varType b') ] of
                        [] -> fail "cannot find equivalent dictionary expression (impossible!)"
                        [t] -> return t
                        _   -> fail "multiple dictionary expressions found (impossible!)"
        lookup2 :: Var -> [(Var,CoreExpr)] -> (Var,CoreExpr)
        lookup2 v l = head [ t | t@(v',_) <- l, v == v' ]
    allDs <- forM dArgs $ \ b -> constT $ do
                if b `elem` uniqDs
                then return $ lookup2 b ds
                else buildSubst b
    transform (\ c -> instsClause (boundVars c) allDs) >>> arr redundantDicts

------------------------------------------------------------------------------

conjunctLemmasT :: (LemmaContext c, HasLemmas m, Monad m) => LemmaName -> LemmaName -> LemmaName -> Transform c m a ()
conjunctLemmasT new lhs rhs = do
    Lemma ql pl _ <- getLemmaByNameT lhs
    Lemma qr pr _ <- getLemmaByNameT rhs
    insertLemmaT new $ Lemma (Conj ql qr) (pl `andP` pr) NotUsed

disjunctLemmasT :: (LemmaContext c, HasLemmas m, Monad m) => LemmaName -> LemmaName -> LemmaName -> Transform c m a ()
disjunctLemmasT new lhs rhs = do
    Lemma ql pl _ <- getLemmaByNameT lhs
    Lemma qr pr _ <- getLemmaByNameT rhs
    insertLemmaT new $ Lemma (Disj ql qr) (pl `orP` pr) NotUsed

implyLemmasT :: (LemmaContext c, HasLemmas m, Monad m) => LemmaName -> LemmaName -> LemmaName -> Transform c m a ()
implyLemmasT new lhs rhs = do
    Lemma ql _  _ <- getLemmaByNameT lhs
    Lemma qr pr _ <- getLemmaByNameT rhs
    insertLemmaT new $ Lemma (Impl lhs ql qr) pr NotUsed

------------------------------------------------------------------------------

mergeQuantifiersR :: MonadCatch m => (Var -> Bool) -> (Var -> Bool) -> Rewrite c m Clause
mergeQuantifiersR pl pr = contextfreeT $ mergeQuantifiers pl pr

mergeQuantifiers :: MonadCatch m => (Var -> Bool) -> (Var -> Bool) -> Clause -> m Clause
mergeQuantifiers pl pr cl = prefixFailMsg "merge-quantifiers failed: " $ do
    (con,lq@(Forall bsl cll),rq@(Forall bsr clr)) <- case cl of
        Conj q1 q2 -> return (Conj,q1,q2)
        Disj q1 q2 -> return (Disj,q1,q2)
        Impl nm q1 q2 -> return (Impl nm,q1,q2)
        _ -> fail "no quantifiers on either side."

    let (lBefore,lbs) = break pl bsl
        (rBefore,rbs) = break pr bsr
        check b q l r = guardMsg (not (b `elemVarSet` freeVarsClause q)) $
                                 "specified "++l++" binder would capture in "++r++"-hand clause."
        checkUB v vs = let fvs = freeVarsVar v
                       in guardMsg (not (any (`elemVarSet` fvs) vs)) $ "binder " ++ getOccString v ++
                            " cannot be floated because it depends on binders not being floated."

    case (lbs,rbs) of
        ([],[])        -> fail "no quantifiers match."
        ([],rb:rAfter) -> do
            check rb lq "right" "left"
            checkUB rb rBefore
            return $ mkForall [rb] $ con lq (mkForall (rBefore++rAfter) clr)
        (lb:lAfter,[]) -> do
            check lb rq "left" "right"
            checkUB lb lBefore
            return $ mkForall [lb] $ con (mkForall (lBefore++lAfter) cll) rq
        (lb:lAfter,rb:rAfter) -> do
            guardMsg (eqType (varType lb) (varType rb)) "specified quantifiers have differing types."
            check lb rq "left" "right"
            check rb lq "right" "left"
            checkUB lb lBefore
            checkUB rb rBefore

            let clr' = substClause rb (varToCoreExpr lb) $ mkForall rAfter clr
                rq' = mkForall rBefore clr'
                lq' = mkForall (lBefore ++ lAfter) cll

            return $ mkForall [lb] (con lq' rq')

------------------------------------------------------------------------------

unshadowClauseR :: MonadUnique m => Rewrite c m Clause
unshadowClauseR = contextfreeT unshadowClause

unshadowClause :: MonadUnique m => Clause -> m Clause
unshadowClause c = go emptySubst (mapUniqSet fs (freeVarsClause c)) c
    where fs = occNameFS . getOccName

          go subst seen (Forall bs cl) = go1 subst seen bs [] cl
          go subst seen (Conj q1 q2) = do
            q1' <- go subst seen q1
            q2' <- go subst seen q2
            return $ Conj q1' q2'
          go subst seen (Disj q1 q2) = do
            q1' <- go subst seen q1
            q2' <- go subst seen q2
            return $ Disj q1' q2'
          go subst seen (Impl nm q1 q2) = do
            q1' <- go subst seen q1
            q2' <- go subst seen q2
            return $ Impl nm q1' q2'
          go subst _ (Equiv e1 e2) =
            let e1' = substExpr (text "unshadowClause e1") subst e1
                e2' = substExpr (text "unshadowClause e2") subst e2
            in return $ Equiv e1' e2'
          go _ _ CTrue = return CTrue

          go1 subst seen []     bs' cl = do
            cl' <- go subst seen cl
            return $ mkForall (reverse bs') cl'
          go1 subst seen (b:bs) bs' cl
            | fsb `elementOfUniqSet` seen = do
                b'' <- cloneVarFSH (inventNames seen) b'
                go1 (extendSubst subst' b' (varToCoreExpr b'')) (addOneToUniqSet seen (fs b'')) bs (b'':bs') cl
            | otherwise = go1 subst' (addOneToUniqSet seen fsb) bs (b':bs') cl
                where fsb = fs b'
                      (subst', b') = substBndr subst b


inventNames :: UniqSet FastString -> FastString -> FastString
inventNames s nm = head [ nm' | i :: Int <- [0..]
                              , let nm' = nm `appendFS` (mkFastString (show i))
                              , not (nm' `elementOfUniqSet` s) ]

------------------------------------------------------------------------------

instantiateClauseVarR :: (Var -> Bool) -> CoreString -> RewriteH Clause
instantiateClauseVarR p cs = prefixFailMsg "instantiation failed: " $ do
    bs <- forallT idR successT const
    e <- case filter p bs of
                [] -> fail "no universally quantified variables match predicate."
                (b:_) | isId b    -> let (before,_) = break (==b) bs
                                     in withVarsInScope before $ parseCoreExprT cs
                      | otherwise -> let (before,_) = break (==b) bs
                                     in liftM (Type . fst) $ withVarsInScope before $ parseTypeWithHolesT cs
    transform (\ c -> instClause (boundVars c) p e) >>> (lintClauseT >> idR) -- lint for sanity

------------------------------------------------------------------------------

-- | Replace all occurrences of the given expression with a new quantified variable.
abstractClauseR :: forall c m.
                       ( AddBindings c, BoundVars c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
                       , LemmaContext c, HasHermitMEnv m, HasLemmas m, LiftCoreM m, MonadCatch m, MonadUnique m )
                    => String -> Transform c m Clause CoreExpr -> Rewrite c m Clause
abstractClauseR nm tr = prefixFailMsg "abstraction failed: " $ do
    e <- tr
    cl <- idR
    b <- constT $ newVarH nm (exprKindOrType e)
    let f = compileFold [Equality [] e (varToCoreExpr b)] -- we don't use mkEquality on purpose, so we can abstract lambdas
    liftM dropBinders $ return (mkForall [b] cl) >>>
                            extractR (anytdR $ promoteExprR $ runFoldR f :: Rewrite c m LCoreTC)

csInQBodyT :: ( AddBindings c, ExtendPath c Crumb, ReadBindings c, ReadPath c Crumb, HasHermitMEnv m, HasLemmas m, LiftCoreM m ) => CoreString -> Transform c m Clause CoreExpr
csInQBodyT cs = forallT successT (parseCoreExprT cs) (flip const)

------------------------------------------------------------------------------

getLemmasT :: (LemmaContext c, HasLemmas m, Monad m) => Transform c m x Lemmas
getLemmasT = contextonlyT $ \ c -> liftM (Map.union (getAntecedents c)) getLemmas

getLemmaByNameT :: (LemmaContext c, HasLemmas m, Monad m) => LemmaName -> Transform c m x Lemma
getLemmaByNameT nm = getLemmasT >>= maybe (fail $ "No lemma named: " ++ show nm) return . Map.lookup nm

------------------------------------------------------------------------------

lemmaBiR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadBindings c, ReadPath c Crumb
            , HasLemmas m, MonadCatch m, MonadUnique m)
         => Used -> LemmaName -> BiRewrite c m CoreExpr
lemmaBiR u nm = afterBiR (beforeBiR (getLemmaByNameT nm) (birewrite . lemmaC)) (markLemmaUsedT nm u >> idR)

lemmaConsequentR :: forall c m. ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadBindings c
                                , ReadPath c Crumb, HasLemmas m, MonadCatch m, MonadUnique m)
                 => Used -> LemmaName -> Rewrite c m Clause
lemmaConsequentR u nm = prefixFailMsg "lemma-consequent failed:" $
                        withPatFailMsg "lemma is not an implication." $ do
    (hs,ante,pat) <- (getLemmaByNameT nm >>^ lemmaC) >>= \case Forall bs (Impl _ ante con) -> return (bs,ante,con)
                                                               Impl _ ante con             -> return ([],ante,con)
    cl' <- transform $ \ c cl -> do
        m <- maybeM ("consequent did not match.") $ lemmaMatch hs pat cl
        subs <- maybeM ("some quantifiers not instantiated.") $
                mapM (\h -> (h,) <$> lookupVarEnv m h) hs
        let cl' = substClauses subs ante
        guardMsg (all (inScope c) $ varSetElems (freeVarsClause cl'))
                 "some variables in result would be out of scope."
        return cl'
    markLemmaUsedT nm u
    return cl'

lemmaConsequentBiR :: forall c m. ( AddBindings c, ExtendPath c Crumb, HasCoreRules c, HasEmptyContext c, LemmaContext c
                                  , ReadBindings c, ReadPath c Crumb, HasHermitMEnv m, HasLemmas m, LiftCoreM m
                                  , MonadCatch m, MonadUnique m)
                   => Used -> LemmaName -> BiRewrite c m CoreExpr
lemmaConsequentBiR u nm = afterBiR (beforeBiR (getLemmaByNameT nm) (go [] . lemmaC)) (markLemmaUsedT nm u >> idR)
    where go :: [CoreBndr] -> Clause -> BiRewrite c m CoreExpr
          go bbs (Forall bs cl) = go (bbs++bs) cl
          go bbs (Impl anteNm ante con) = do
            let con' = mkForall bbs con
                bs = forallQs con'
                eqs = toEqualities con'
                foldUnfold side f = do
                    (cl,e) <- transform $ \ c e -> do
                                let cf = compileFold $ map f eqs
                                (e',hs) <- maybeM ("expression did not match "++side++"-hand side") $ runFoldMatches cf c e
                                let matches = [ case lookupVarEnv hs b of
                                                    Nothing -> Left b
                                                    Just arg -> Right (b,arg)
                                              | b <- bs ]
                                    (unmatched, subs) = partitionEithers matches
                                    acl = substClauses subs ante
                                    cl = mkForall unmatched acl
                                return (cl,e')
                    verifyOrCreateT u anteNm cl
                    return e
            bidirectional (foldUnfold "left" id) (foldUnfold "right" flipEquality)
          go _ _ = let t = fail $ show nm ++ " is not an implication."
                   in bidirectional t t

------------------------------------------------------------------------------

insertLemmaT :: (HasLemmas m, Monad m) => LemmaName -> Lemma -> Transform c m a ()
insertLemmaT nm l = constT $ insertLemma nm l

insertLemmasT :: (HasLemmas m, Monad m) => [NamedLemma] -> Transform c m a ()
insertLemmasT = constT . mapM_ (uncurry insertLemma)

modifyLemmaT :: (LemmaContext c, HasLemmas m, Monad m)
             => LemmaName
             -> (LemmaName -> LemmaName) -- ^ modify lemma name
             -> Rewrite c m Clause       -- ^ rewrite the quantified clause
             -> (Proven -> Proven)       -- ^ modify proven status
             -> (Used -> Used)           -- ^ modify used status
             -> Transform c m a ()
modifyLemmaT nm nFn rr pFn uFn = do
    Lemma cl p u <- getLemmaByNameT nm
    cl' <- rr <<< return cl
    constT $ insertLemma (nFn nm) $ Lemma cl' (pFn p) (uFn u)

markLemmaUsedT :: (LemmaContext c, HasLemmas m, MonadCatch m) => LemmaName -> Used -> Transform c m a ()
markLemmaUsedT nm u = ifM (lemmaExistsT nm) (modifyLemmaT nm id idR id (const u)) (return ())

markLemmaProvenT :: (LemmaContext c, HasLemmas m, MonadCatch m) => LemmaName -> Proven -> Transform c m a ()
markLemmaProvenT nm p = ifM (lemmaExistsT nm) (modifyLemmaT nm id idR (const p) id) (return ())

lemmaExistsT :: (LemmaContext c, HasLemmas m, MonadCatch m) => LemmaName -> Transform c m a Bool
lemmaExistsT nm = constT $ Map.member nm <$> getLemmas

------------------------------------------------------------------------------

lemmaNameToClauseT :: (LemmaContext c, HasLemmas m, Monad m) => LemmaName -> Transform c m x Clause
lemmaNameToClauseT nm = liftM lemmaC $ getLemmaByNameT nm

-- | @e@ ==> @let v = lhs in e@  (also works in a similar manner at Program nodes)
lemmaLhsIntroR :: LemmaName -> RewriteH Core
lemmaLhsIntroR = lemmaNameToClauseT >=> eqLhsIntroR

-- | @e@ ==> @let v = rhs in e@  (also works in a similar manner at Program nodes)
lemmaRhsIntroR :: LemmaName -> RewriteH Core
lemmaRhsIntroR = lemmaNameToClauseT >=> eqRhsIntroR

------------------------------------------------------------------------------

-- Little DSL for building composite lemmas

infixr 5 -->

(-->) :: Type -> Type -> Type
(-->) = mkFunTy

infixr 3 ==>

(==>) :: (LemmaName, Clause) -> Clause -> Clause
(==>) = uncurry Impl

infixr 5 /\

(/\) :: Clause -> Clause -> Clause
(/\) = Conj

infixr 4 \/

(\/) :: Clause -> Clause -> Clause
(\/) = Disj

infix 8 ===

(===) :: (ToCoreExpr a, ToCoreExpr b) => a -> b -> Clause
lhs === rhs = Equiv (toCE lhs) (toCE rhs)

infixl 9 $$

($$) :: (ToCoreExpr a, ToCoreExpr b, MonadCatch m) => a -> b -> m CoreExpr
f $$ e = buildAppM (toCE f) (toCE e)

($$$) :: (ToCoreExpr a, ToCoreExpr b, MonadCatch m) => a -> [b] -> m CoreExpr
f $$$ es = buildAppsM (toCE f) (map toCE es)

class ToCoreExpr a where
    toCE :: a -> CoreExpr

deriving instance Typeable ToCoreExpr

instance ToCoreExpr CoreExpr where toCE = id

instance ToCoreExpr Var where toCE = varToCoreExpr

instance ToCoreExpr Type where toCE = Type

-- Create new lemma library with single unproven lemma.
newLemma :: LemmaName -> Clause -> Map.Map LemmaName Lemma
newLemma nm cl = Map.singleton nm (Lemma cl NotProven NotUsed)
