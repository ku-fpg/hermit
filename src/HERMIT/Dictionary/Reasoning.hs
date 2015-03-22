{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
    , ppQuantifiedT
    , ppLCoreTCT
      -- ** Lifting transformations over 'Quantified'
    , lhsT
    , rhsT
    , bothT
    , lhsR
    , rhsR
    , bothR
    , verifyQuantifiedT
    , lemmaR
    , quantIdentitiesR
    , reflexivityClauseR
    , verifyOrCreateT
    , verifyEqualityLeftToRightT
    , verifyEqualityCommonTargetT
    , verifyIsomorphismT
    , verifyRetractionT
    , reflexivityR
    , simplifyQuantifiedR
    , retractionBR
    , unshadowQuantifiedR
    , instantiateDictsR
    , instantiateQuantifiedVarR
    , abstractQuantifiedR
    , discardUniVars
    ) where

import           Control.Arrow hiding ((<+>))
import           Control.Monad

import           Data.Either (partitionEithers)
import           Data.List (isInfixOf, nubBy)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Monoid

import           HERMIT.Context
import           HERMIT.Core
import           HERMIT.External
import           HERMIT.GHC hiding ((<>), (<+>), nest, ($+$))
import           HERMIT.Kure
import           HERMIT.Lemma
import           HERMIT.Monad
import           HERMIT.Name
import           HERMIT.ParserCore
import           HERMIT.ParserType
import           HERMIT.PrettyPrinter.Common
import           HERMIT.PrettyPrinter.Clean (symbol) -- this should be in Common
import           HERMIT.Utilities

import           HERMIT.Dictionary.Common
import           HERMIT.Dictionary.Fold hiding (externals)
import           HERMIT.Dictionary.GHC hiding (externals)
import           HERMIT.Dictionary.Local.Let (nonRecIntroR)

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
    , external "unshadow-quantified" (promoteQuantifiedR unshadowQuantifiedR :: RewriteH LCoreTC)
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
        [ "conjunt new-name lhs-name rhs-name" ]
    , external "disjunct" (\n1 n2 n3 -> disjunctLemmasT n1 n2 n3 :: TransformH LCore ())
        [ "disjunt new-name lhs-name rhs-name" ]
    , external "imply" (\n1 n2 n3 -> implyLemmasT n1 n2 n3 :: TransformH LCore ())
        [ "imply new-name antecedent-name consequent-name" ]
    , external "lemma-birewrite" (promoteExprBiR . lemmaBiR Obligation :: LemmaName -> BiRewriteH LCore)
        [ "Generate a bi-directional rewrite from a lemma." ]
    , external "lemma-forward" (forwardT . promoteExprBiR . lemmaBiR Obligation :: LemmaName -> RewriteH LCore)
        [ "Generate a rewrite from a lemma, left-to-right." ]
    , external "lemma-backward" (backwardT . promoteExprBiR . lemmaBiR Obligation :: LemmaName -> RewriteH LCore)
        [ "Generate a rewrite from a lemma, right-to-left." ]
    , external "lemma-consequent" (promoteQuantifiedR . lemmaConsequentR Obligation :: LemmaName -> RewriteH LCore)
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
    , external "inst-lemma" (\ nm v cs -> modifyLemmaT nm id (instantiateQuantifiedVarR (cmpHN2Var v) cs) id id :: TransformH LCore ())
        [ "Instantiate one of the universally quantified variables of the given lemma,"
        , "with the given Core expression, creating a new lemma. Instantiating an"
        , "already proven lemma will result in the new lemma being considered proven." ]
    , external "inst-dictionaries" (promoteQuantifiedR instantiateDictsR :: RewriteH LCore)
        [ "Instantiate all of the universally quantified dictionaries of the given lemma." ]
    , external "abstract" ((\nm -> promoteQuantifiedR . abstractQuantifiedR nm . csInQBodyT) :: String -> CoreString -> RewriteH LCore)
        [ "Weaken a lemma by abstracting an expression to a new quantifier." ]
    , external "abstract" ((\nm rr -> promoteQuantifiedR $ abstractQuantifiedR nm $ extractT rr >>> setFailMsg "path must focus on an expression" projectT) :: String -> RewriteH LCore -> RewriteH LCore)
        [ "Weaken a lemma by abstracting an expression to a new quantifier." ]
    , external "copy-lemma" (\ nm newName -> modifyLemmaT nm (const newName) idR id id :: TransformH LCore ())
        [ "Copy a given lemma, with a new name." ]
    , external "modify-lemma" ((\ nm rr -> modifyLemmaT nm id (extractR rr) (const NotProven) (const NotUsed)) :: LemmaName -> RewriteH LCore -> TransformH LCore ())
        [ "Modify a given lemma. Resets proven status to Not Proven and used status to Not Used." ]
    , external "query-lemma" ((\ nm t -> getLemmaByNameT nm >>> arr lemmaQ >>> extractT t) :: LemmaName -> TransformH LCore String -> TransformH LCore String)
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
    , external "lhs" (promoteQuantifiedR . lhsR :: RewriteH LCore -> RewriteH LCore)
        [ "Apply a rewrite to the LHS of a quantified clause." ]
    , external "lhs" (promoteQuantifiedT . lhsT :: TransformH LCore String -> TransformH LCore String)
        [ "Apply a transformation to the LHS of a quantified clause." ]
    , external "rhs" (promoteQuantifiedR . rhsR :: RewriteH LCore -> RewriteH LCore)
        [ "Apply a rewrite to the RHS of a quantified clause." ]
    , external "rhs" (promoteQuantifiedT . rhsT :: TransformH LCore String -> TransformH LCore String)
        [ "Apply a transformation to the RHS of a quantified clause." ]
    , external "both" (promoteQuantifiedR . bothR :: RewriteH LCore -> RewriteH LCore)
        [ "Apply a rewrite to both sides of an equality, succeeding if either succeed." ]
    , external "both" ((\t -> do (r,s) <- promoteQuantifiedT (bothT t); return (unlines [r,s])) :: TransformH LCore String -> TransformH LCore String)
        [ "Apply a transformation to both sides of a quantified clause." ]
    , external "reflexivity" (reflexivityR :: RewriteH LCore)
        [ "Rewrite alpha-equivalence to true." ]
    , external "simplify-proof" (simplifyQuantifiedR :: RewriteH LCore)
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
extensionalityR :: Maybe String -> Rewrite c HermitM Quantified
extensionalityR mn = prefixFailMsg "extensionality failed: " $
  do Quantified vs (Equiv lhs rhs) <- idR

     let tyL = exprKindOrType lhs
         tyR = exprKindOrType rhs
     guardMsg (tyL `typeAlphaEq` tyR) "type mismatch between sides of equality.  This shouldn't happen, so is probably a bug."

     -- TODO: use the fresh-name-generator in AlphaConversion to avoid shadowing.
     (_,argTy,_) <- splitFunTypeM tyL
     v <- constT $ newVarH (fromMaybe "x" mn) argTy

     let x = varToCoreExpr v

     return $ Quantified (vs ++ [v]) $ Equiv (mkCoreApp lhs x) (mkCoreApp rhs x)

------------------------------------------------------------------------------

-- | @e@ ==> @let v = lhs in e@
eqLhsIntroR :: Quantified -> Rewrite c HermitM Core
eqLhsIntroR (Quantified bs (Equiv lhs _)) = nonRecIntroR "lhs" (mkCoreLams bs lhs)
eqLhsIntroR _                             = fail "compound lemmas not supported."

-- | @e@ ==> @let v = rhs in e@
eqRhsIntroR :: Quantified -> Rewrite c HermitM Core
eqRhsIntroR (Quantified bs (Equiv _ rhs)) = nonRecIntroR "rhs" (mkCoreLams bs rhs)
eqRhsIntroR _                             = fail "compound lemmas not supported."

------------------------------------------------------------------------------

-- | Create a 'BiRewrite' from a 'Quantified'.
birewrite :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c
             , ReadPath c Crumb, MonadCatch m, MonadUnique m )
          => Quantified -> BiRewrite c m CoreExpr
birewrite q = bidirectional (foldUnfold "left" id) (foldUnfold "right" flipEquality)
    where foldUnfold side f = transform $ \ c ->
                                maybeM ("expression did not match "++side++"-hand side")
                                . fold (map f (toEqualities q)) c

------------------------------------------------------------------------------
-- TODO: deprecate these?
-- Yes, but later.  They're in the paper now.
-- We should be using "childR crumb", really.

-- | Lift a transformation over 'LCoreTC' into a transformation over the left-hand side of a 'Quantified'.
lhsT :: (AddBindings c, LemmaContext c, ReadPath c Crumb, ExtendPath c Crumb, Monad m)
     => Transform c m LCore a -> Transform c m Quantified a
lhsT t = quantifiedT successT (clauseT t successT (\_ l _ -> l) (fail "applied to true.")) (flip const)

-- | Lift a transformation over 'LCoreTC' into a transformation over the right-hand side of a 'Quantified'.
rhsT :: (AddBindings c, LemmaContext c, ReadPath c Crumb, ExtendPath c Crumb, Monad m)
     => Transform c m LCore a -> Transform c m Quantified a
rhsT t = quantifiedT successT (clauseT successT t (\_ _ r -> r) (fail "applied to true.")) (flip const)

-- | Lift a transformation over 'LCoreTC' into a transformation over both sides of a 'Quantified'.
bothT :: (AddBindings c, LemmaContext c, ReadPath c Crumb, ExtendPath c Crumb, Monad m)
      => Transform c m LCore a -> Transform c m Quantified (a, a)
bothT t = quantifiedT successT (clauseT t t (const (,)) (fail "applied to true.")) (flip const)

-- | Lift a rewrite over 'LCoreTC' into a rewrite over the left-hand side of a 'Quantified'.
lhsR :: (AddBindings c, Monad m, LemmaContext c, ReadPath c Crumb, ExtendPath c Crumb)
     => Rewrite c m LCore -> Rewrite c m Quantified
lhsR r = quantifiedR idR (clauseR r idR)

-- | Lift a rewrite over 'LCoreTC' into a rewrite over the right-hand side of a 'Quantified'.
rhsR :: (AddBindings c, Monad m, LemmaContext c, ReadPath c Crumb, ExtendPath c Crumb)
     => Rewrite c m LCore -> Rewrite c m Quantified
rhsR r = quantifiedR idR (clauseR idR r)

-- | Lift a rewrite over 'LCoreTC' into a rewrite over both sides of a 'Quantified'.
bothR :: (AddBindings c, MonadCatch m, LemmaContext c, ReadPath c Crumb, ExtendPath c Crumb)
      => Rewrite c m LCore -> Rewrite c m Quantified
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
    qDoc <- return q >>> ppQuantifiedT pp
    let hDoc = PP.text (show nm) PP.<+> PP.text ("(" ++ show p ++ ")")
    return $ hDoc PP.$+$ PP.nest 2 qDoc

ppLCoreTCT :: PrettyPrinter -> PrettyH LCoreTC
ppLCoreTCT pp = promoteT (ppQuantifiedT pp) <+ promoteT (ppClauseT pp) <+ promoteT (pCoreTC pp)

ppQuantifiedT :: PrettyPrinter -> PrettyH Quantified
ppQuantifiedT pp = do
    (d1,d2) <- quantifiedT (pForall pp) (ppClauseT pp) (,)
    return $ PP.sep [d1,d2]

ppClauseT :: PrettyPrinter -> PrettyH Clause
ppClauseT pp = do
    let t = absPathT &&& (promoteT (ppQuantifiedT pp) <+ promoteT (extractT (pCoreTC pp) :: PrettyH Core)) -- TODO: temporary hack, need to think about what's going on here and fix it
        parenify (p1,d1) (p2,d2) o = ( symbol p1 '(' PP.<> d1 PP.<> symbol p1 ')'
                                     , symbol p2 '(' PP.<> d2 PP.<> symbol p2 ')'
                                     , syntaxColor (PP.text o)
                                     )
    (d1,d2,oper) <- clauseT t t (\ cl r1 r2 ->
                                    case cl of
                                        Conj {} -> parenify r1 r2 "^"
                                        Disj {} -> parenify r1 r2 "v"
                                        Impl {} -> parenify r1 r2 "=>"
                                        Equiv {} -> (snd r1, snd r2, syntaxColor $ PP.text "=")
                                        CTrue   -> error "impossible case: applied to true")
                                (return (syntaxColor (PP.text "true"), PP.empty, PP.empty))
    return $ PP.sep [d1,oper,d2]

------------------------------------------------------------------------------

verifyQuantifiedT :: (AddBindings c, ReadPath c Crumb, ExtendPath c Crumb, MonadCatch m) => Transform c m Quantified ()
verifyQuantifiedT = setFailMsg "verification failed: clause must be true (perhaps try reflexivity first)" $ do
    Quantified _ CTrue <- idR
    return ()

lemmaR :: (LemmaContext c, HasLemmas m, MonadCatch m) => Used -> LemmaName -> Rewrite c m Clause
lemmaR used nm = prefixFailMsg "verification failed: " $ do
    Lemma q _ _ <- getLemmaByNameT nm
    eq <- arr (q `proves`)
    guardMsg eq "lemmas are not equivalent."
    markLemmaUsedT nm used
    return CTrue

verifyOrCreateT :: ( HasCoreRules c, LemmaContext c, ReadBindings c, ReadPath c Crumb
                   , HasDebugChan m, HasLemmas m, MonadCatch m )
                => Used -> LemmaName -> Quantified -> Transform c m a ()
verifyOrCreateT u nm q@(Quantified _ cl)  = do
    exists <- testM $ getLemmaByNameT nm
    if exists
    then do CTrue <- return cl >>> lemmaR u nm ; return ()
    else contextonlyT $ \ c -> sendKEnvMessage $ AddObligation (toHermitC c) nm $ Lemma q NotProven u

reflexivityR :: (AddBindings c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m) => Rewrite c m LCore
reflexivityR = promoteR (quantifiedR idR reflexivityClauseR) <+ promoteR reflexivityClauseR

reflexivityClauseR :: Monad m => Rewrite c m Clause
reflexivityClauseR = do
    Equiv lhs rhs <- idR
    guardMsg (exprAlphaEq lhs rhs) "the two sides are not alpha-equivalent."
    return CTrue

simplifyQuantifiedR :: (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadPath c Crumb, MonadCatch m)
                    => Rewrite c m LCore
simplifyQuantifiedR = anybuR (promoteR quantIdentitiesR <+ promoteR reflexivityClauseR)

quantIdentitiesR :: MonadCatch m => Rewrite c m Quantified
quantIdentitiesR =
    trueConjLR <+ trueConjRR <+
    trueDisjLR <+ trueDisjRR <+
    trueImpliesR <+ impliesTrueR

trueConjLR :: Monad m => Rewrite c m Quantified
trueConjLR = do
    Quantified bs (Conj (Quantified _ CTrue) (Quantified bs' cl)) <- idR
    return $ Quantified (bs++bs') cl

trueConjRR :: Monad m => Rewrite c m Quantified
trueConjRR = do
    Quantified bs (Conj (Quantified bs' cl) (Quantified _ CTrue)) <- idR
    return $ Quantified (bs++bs') cl

trueDisjLR :: Monad m => Rewrite c m Quantified
trueDisjLR = do
    Quantified _ (Disj (Quantified _ CTrue) _) <- idR
    return $ Quantified [] CTrue

trueDisjRR :: Monad m => Rewrite c m Quantified
trueDisjRR = do
    Quantified _ (Disj _ (Quantified _ CTrue)) <- idR
    return $ Quantified [] CTrue

trueImpliesR :: Monad m => Rewrite c m Quantified
trueImpliesR = do
    Quantified bs (Impl _ (Quantified _ CTrue) (Quantified bs' cl)) <- idR
    return $ Quantified (bs++bs') cl

impliesTrueR :: Monad m => Rewrite c m Quantified
impliesTrueR = do
    Quantified _ (Impl _ _ (Quantified _ CTrue)) <- idR
    return $ Quantified [] CTrue

splitAntecedentR :: MonadCatch m => Rewrite c m Clause
splitAntecedentR = prefixFailMsg "antecedent split failed: " $
                   withPatFailMsg (wrongExprForm "(ante1 ^ ante2) => con") $ do
    Impl nm (Quantified bs (Conj (Quantified abs1 c1) (Quantified abs2 c2))) con <- idR
    return $ Impl (nm <> "0") (Quantified (bs++abs1) c1)
                              (Quantified [] (Impl (nm <> "1") (Quantified (bs++abs2) c2) con))


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
instantiateDictsR :: RewriteH Quantified
instantiateDictsR = prefixFailMsg "Dictionary instantiation failed: " $ do
    bs <- forallVarsT idR
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
    transform (\ c -> instsQuantified (boundVars c) allDs) >>> arr redundantDicts

------------------------------------------------------------------------------

conjunctLemmasT :: (LemmaContext c, HasLemmas m, Monad m) => LemmaName -> LemmaName -> LemmaName -> Transform c m a ()
conjunctLemmasT new lhs rhs = do
    Lemma ql pl _ <- getLemmaByNameT lhs
    Lemma qr pr _ <- getLemmaByNameT rhs
    insertLemmaT new $ Lemma (Quantified [] (Conj ql qr)) (pl `andP` pr) NotUsed

disjunctLemmasT :: (LemmaContext c, HasLemmas m, Monad m) => LemmaName -> LemmaName -> LemmaName -> Transform c m a ()
disjunctLemmasT new lhs rhs = do
    Lemma ql pl _ <- getLemmaByNameT lhs
    Lemma qr pr _ <- getLemmaByNameT rhs
    insertLemmaT new $ Lemma (Quantified [] (Disj ql qr)) (pl `orP` pr) NotUsed

implyLemmasT :: (LemmaContext c, HasLemmas m, Monad m) => LemmaName -> LemmaName -> LemmaName -> Transform c m a ()
implyLemmasT new lhs rhs = do
    Lemma ql _  _ <- getLemmaByNameT lhs
    Lemma qr pr _ <- getLemmaByNameT rhs
    insertLemmaT new $ Lemma (Quantified [] (Impl lhs ql qr)) pr NotUsed

------------------------------------------------------------------------------

mergeQuantifiersR :: MonadCatch m => (Var -> Bool) -> (Var -> Bool) -> Rewrite c m Quantified
mergeQuantifiersR pl pr = contextfreeT $ mergeQuantifiers pl pr

mergeQuantifiers :: MonadCatch m => (Var -> Bool) -> (Var -> Bool) -> Quantified -> m Quantified
mergeQuantifiers pl pr (Quantified bs cl) = prefixFailMsg "merge-quantifiers failed: " $ do
    (con,lq@(Quantified bsl cll),rq@(Quantified bsr clr)) <- case cl of
        Conj q1 q2 -> return (Conj,q1,q2)
        Disj q1 q2 -> return (Disj,q1,q2)
        Impl nm q1 q2 -> return (Impl nm,q1,q2)
        _ -> fail "no quantifiers on either side."

    let (lBefore,lbs) = break pl bsl
        (rBefore,rbs) = break pr bsr
        check b q l r = guardMsg (not (b `elemVarSet` freeVarsQuantified q)) $
                                 "specified "++l++" binder would capture in "++r++"-hand clause."
        checkUB v vs = let fvs = freeVarsVar v
                       in guardMsg (not (any (`elemVarSet` fvs) vs)) $ "binder " ++ getOccString v ++
                            " cannot be floated because it depends on binders not being floated."

    case (lbs,rbs) of
        ([],[])        -> fail "no quantifiers match."
        ([],rb:rAfter) -> do
            check rb lq "right" "left"
            checkUB rb rBefore
            return $ Quantified (bs++[rb]) $ con lq (Quantified (rBefore++rAfter) clr)
        (lb:lAfter,[]) -> do
            check lb rq "left" "right"
            checkUB lb lBefore
            return $ Quantified (bs++[lb]) $ con (Quantified (lBefore++lAfter) cll) rq
        (lb:lAfter,rb:rAfter) -> do
            guardMsg (eqType (varType lb) (varType rb)) "specified quantifiers have differing types."
            check lb rq "left" "right"
            check rb lq "right" "left"
            checkUB lb lBefore
            checkUB rb rBefore

            let Quantified partial clr' = substQuantified rb (varToCoreExpr lb) $ Quantified rAfter clr
                rq' = Quantified (rBefore ++ partial) clr'
                lq' = Quantified (lBefore ++ lAfter) cll

            return $ Quantified (bs++[lb]) (con lq' rq')

------------------------------------------------------------------------------

unshadowQuantifiedR :: MonadUnique m => Rewrite c m Quantified
unshadowQuantifiedR = contextfreeT unshadowQuantified

unshadowQuantified :: MonadUnique m => Quantified -> m Quantified
unshadowQuantified q = go emptySubst (mapUniqSet fs (freeVarsQuantified q)) q
    where fs = occNameFS . getOccName

          go subst seen (Quantified bs cl) = go1 subst seen bs [] cl

          go1 subst seen []     bs' cl = do
            cl' <- go2 subst seen cl
            return $ Quantified (reverse bs') cl'
          go1 subst seen (b:bs) bs' cl
            | fsb `elementOfUniqSet` seen = do
                b'' <- cloneVarFSH (inventNames seen) b'
                go1 (extendSubst subst' b' (varToCoreExpr b'')) (addOneToUniqSet seen (fs b'')) bs (b'':bs') cl
            | otherwise = go1 subst' (addOneToUniqSet seen fsb) bs (b':bs') cl
                where fsb = fs b'
                      (subst', b') = substBndr subst b

          go2 subst seen (Conj q1 q2) = do
            q1' <- go subst seen q1
            q2' <- go subst seen q2
            return $ Conj q1' q2'
          go2 subst seen (Disj q1 q2) = do
            q1' <- go subst seen q1
            q2' <- go subst seen q2
            return $ Disj q1' q2'
          go2 subst seen (Impl nm q1 q2) = do
            q1' <- go subst seen q1
            q2' <- go subst seen q2
            return $ Impl nm q1' q2'
          go2 subst _ (Equiv e1 e2) =
            let e1' = substExpr (text "unshadowQuantified e1") subst e1
                e2' = substExpr (text "unshadowQuantified e2") subst e2
            in return $ Equiv e1' e2'
          go2 _ _ CTrue = return CTrue

inventNames :: UniqSet FastString -> FastString -> FastString
inventNames s nm = head [ nm' | i :: Int <- [0..]
                              , let nm' = nm `appendFS` (mkFastString (show i))
                              , not (nm' `elementOfUniqSet` s) ]

------------------------------------------------------------------------------

instantiateQuantifiedVarR :: (Var -> Bool) -> CoreString -> RewriteH Quantified
instantiateQuantifiedVarR p cs = prefixFailMsg "instantiation failed: " $ do
    bs <- forallVarsT idR
    e <- case filter p bs of
                [] -> fail "no universally quantified variables match predicate."
                (b:_) | isId b    -> let (before,_) = break (==b) bs
                                     in withVarsInScope before $ parseCoreExprT cs
                      | otherwise -> let (before,_) = break (==b) bs
                                     in liftM (Type . fst) $ withVarsInScope before $ parseTypeWithHolesT cs
    transform (\ c -> instQuantified (boundVars c) p e) >>> (lintQuantifiedT >> idR) -- lint for sanity

------------------------------------------------------------------------------

-- | Replace all occurrences of the given expression with a new quantified variable.
abstractQuantifiedR :: forall c m.
                       ( AddBindings c, BoundVars c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
                       , LemmaContext c, HasDebugChan m, HasHermitMEnv m, HasLemmas m, LiftCoreM m, MonadCatch m, MonadUnique m )
                    => String -> Transform c m Quantified CoreExpr -> Rewrite c m Quantified
abstractQuantifiedR nm tr = prefixFailMsg "abstraction failed: " $ do
    e <- tr
    Quantified bs cl <- idR
    b <- constT $ newVarH nm (exprKindOrType e)
    let f = compileFold [Equality [] e (varToCoreExpr b)] -- we don't use mkEquality on purpose, so we can abstract lambdas
    liftM dropBinders $ return (Quantified (bs++[b]) cl) >>>
                            extractR (anytdR $ promoteExprR $ runFoldR f :: Rewrite c m LCoreTC)

csInQBodyT :: ( AddBindings c, ReadBindings c, ReadPath c Crumb, HasDebugChan m, HasHermitMEnv m, HasLemmas m, LiftCoreM m ) => CoreString -> Transform c m Quantified CoreExpr
csInQBodyT cs = do
    Quantified bs _ <- idR
    withVarsInScope bs $ parseCoreExprT cs

------------------------------------------------------------------------------

getLemmasT :: (LemmaContext c, HasLemmas m, Monad m) => Transform c m x Lemmas
getLemmasT = contextonlyT $ \ c -> liftM (Map.union (getAntecedents c)) getLemmas

getLemmaByNameT :: (LemmaContext c, HasLemmas m, Monad m) => LemmaName -> Transform c m x Lemma
getLemmaByNameT nm = getLemmasT >>= maybe (fail $ "No lemma named: " ++ show nm) return . Map.lookup nm

------------------------------------------------------------------------------

lemmaBiR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadBindings c, ReadPath c Crumb
            , HasLemmas m, MonadCatch m, MonadUnique m)
         => Used -> LemmaName -> BiRewrite c m CoreExpr
lemmaBiR u nm = afterBiR (beforeBiR (getLemmaByNameT nm) (birewrite . lemmaQ)) (markLemmaUsedT nm u >> idR)

lemmaConsequentR :: forall c m. ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadBindings c
                                , ReadPath c Crumb, HasLemmas m, MonadCatch m, MonadUnique m)
                 => Used -> LemmaName -> Rewrite c m Quantified
lemmaConsequentR u nm = prefixFailMsg "lemma-consequent failed:" $
                        withPatFailMsg "lemma is not an implication." $ do
    Quantified hs (Impl _ ante con) <- lemmaQ <$> getLemmaByNameT nm
    q' <- transform $ \ c q -> do
        m <- maybeM ("consequent did not match.") $ lemmaMatch hs con q
        subs <- maybeM ("some quantifiers not instantiated.") $
                mapM (\h -> (h,) <$> lookupVarEnv m h) hs
        let q' = substQuantifieds subs ante
        guardMsg (all (inScope c) $ varSetElems (freeVarsQuantified q'))
                 "some variables in result would be out of scope."
        return q'
    markLemmaUsedT nm u
    return q'

lemmaConsequentBiR :: forall c m. ( AddBindings c, ExtendPath c Crumb, HasCoreRules c, HasEmptyContext c, LemmaContext c
                                  , ReadBindings c, ReadPath c Crumb, HasDebugChan m, HasLemmas m, MonadCatch m
                                  , MonadUnique m)
                   => Used -> LemmaName -> BiRewrite c m CoreExpr
lemmaConsequentBiR u nm = afterBiR (beforeBiR (getLemmaByNameT nm) (go . lemmaQ)) (markLemmaUsedT nm u >> idR)
    where go :: Quantified -> BiRewrite c m CoreExpr
          go (Quantified bs (Impl anteNm ante (Quantified bs' cl))) = do
            let eqs = toEqualities $ Quantified (bs++bs') cl -- consequent
                foldUnfold side f = do
                    (q,e) <- transform $ \ c e -> do
                                let cf = compileFold $ map f eqs
                                (e',hs) <- maybeM ("expression did not match "++side++"-hand side") $ runFoldMatches cf c e
                                let matches = [ case lookupVarEnv hs b of
                                                    Nothing -> Left b
                                                    Just arg -> Right (b,arg)
                                              | b <- bs ]
                                    (unmatched, subs) = partitionEithers matches
                                    Quantified aBs acl = substQuantifieds subs ante
                                    q = Quantified (unmatched++aBs) acl
                                return (q,e')
                    verifyOrCreateT u anteNm q
                    return e
            bidirectional (foldUnfold "left" id) (foldUnfold "right" flipEquality)
          go _ = let t = fail $ show nm ++ " is not an implication."
                 in bidirectional t t

------------------------------------------------------------------------------

insertLemmaT :: (HasLemmas m, Monad m) => LemmaName -> Lemma -> Transform c m a ()
insertLemmaT nm l = constT $ insertLemma nm l

insertLemmasT :: (HasLemmas m, Monad m) => [NamedLemma] -> Transform c m a ()
insertLemmasT = constT . mapM_ (uncurry insertLemma)

modifyLemmaT :: (LemmaContext c, HasLemmas m, Monad m)
             => LemmaName
             -> (LemmaName -> LemmaName) -- ^ modify lemma name
             -> Rewrite c m Quantified   -- ^ rewrite the quantified clause
             -> (Proven -> Proven)       -- ^ modify proven status
             -> (Used -> Used)           -- ^ modify used status
             -> Transform c m a ()
modifyLemmaT nm nFn rr pFn uFn = do
    Lemma q p u <- getLemmaByNameT nm
    q' <- rr <<< return q
    constT $ insertLemma (nFn nm) $ Lemma q' (pFn p) (uFn u)

markLemmaUsedT :: (LemmaContext c, HasLemmas m, MonadCatch m) => LemmaName -> Used -> Transform c m a ()
markLemmaUsedT nm u = ifM (lemmaExistsT nm) (modifyLemmaT nm id idR id (const u)) (return ())

markLemmaProvenT :: (LemmaContext c, HasLemmas m, MonadCatch m) => LemmaName -> Proven -> Transform c m a ()
markLemmaProvenT nm p = ifM (lemmaExistsT nm) (modifyLemmaT nm id idR (const p) id) (return ())

lemmaExistsT :: (LemmaContext c, HasLemmas m, MonadCatch m) => LemmaName -> Transform c m a Bool
lemmaExistsT nm = constT $ Map.member nm <$> getLemmas

------------------------------------------------------------------------------

lemmaNameToQuantifiedT :: (LemmaContext c, HasLemmas m, Monad m) => LemmaName -> Transform c m x Quantified
lemmaNameToQuantifiedT nm = liftM lemmaQ $ getLemmaByNameT nm

-- | @e@ ==> @let v = lhs in e@  (also works in a similar manner at Program nodes)
lemmaLhsIntroR :: LemmaName -> RewriteH Core
lemmaLhsIntroR = lemmaNameToQuantifiedT >=> eqLhsIntroR

-- | @e@ ==> @let v = rhs in e@  (also works in a similar manner at Program nodes)
lemmaRhsIntroR :: LemmaName -> RewriteH Core
lemmaRhsIntroR = lemmaNameToQuantifiedT >=> eqRhsIntroR

------------------------------------------------------------------------------
