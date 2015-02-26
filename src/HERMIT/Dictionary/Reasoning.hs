{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
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
    , lemmaR
    , markLemmaUsedT
    , markLemmaProvedT
    , modifyLemmaT
    , showLemmaT
    , showLemmasT
    , ppLemmaT
    , ppQuantifiedT
      -- ** Lifting transformations over 'Quantified'
    , core2qcT
    , core2qcR
    , lhsT
    , rhsT
    , bothT
    , lhsR
    , rhsR
    , bothR
    , forallVarsT
    , verifyQuantifiedT
    , lintQuantifiedT
    , verifyEqualityLeftToRightT
    , verifyEqualityCommonTargetT
    , verifyIsomorphismT
    , verifyRetractionT
    , retractionBR
    , unshadowQuantifiedR
    , instantiateDictsR
    , instantiateQuantified
    , instantiateQuantifiedVar
    , instantiateQuantifiedVarR
    , discardUniVars
    ) where

import           Control.Arrow hiding ((<+>))
import           Control.Monad

import qualified Data.Map as Map
import           Data.List (isInfixOf, nubBy)
import           Data.Maybe (fromMaybe)

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
import           HERMIT.Utilities

import           HERMIT.Dictionary.Common
import           HERMIT.Dictionary.Fold hiding (externals)
import           HERMIT.Dictionary.GHC hiding (externals)
import           HERMIT.Dictionary.Local.Let (nonRecIntroR)

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
    , external "unshadow" (promoteR unshadowQuantifiedR :: RewriteH QC)
        [ "Unshadow a quantified clause." ]
    , external "lemma" (promoteExprBiR . lemmaR :: LemmaName -> BiRewriteH Core)
        [ "Generate a bi-directional rewrite from a lemma." ]
    , external "lemma-lhs-intro" (lemmaLhsIntroR :: LemmaName -> RewriteH Core)
        [ "Introduce the LHS of a lemma as a non-recursive binding, in either an expression or a program."
        , "body ==> let v = lhs in body" ] .+ Introduce .+ Shallow
    , external "lemma-rhs-intro" (lemmaRhsIntroR :: LemmaName -> RewriteH Core)
        [ "Introduce the RHS of a lemma as a non-recursive binding, in either an expression or a program."
        , "body ==> let v = rhs in body" ] .+ Introduce .+ Shallow
    , external "inst-lemma" (\ nm v cs -> modifyLemmaT nm id (instantiateQuantifiedVarR (cmpString2Var v) cs) id id :: TransformH Core ())
        [ "Instantiate one of the universally quantified variables of the given lemma,"
        , "with the given Core expression, creating a new lemma. Instantiating an"
        , "already proven lemma will result in the new lemma being considered proven." ]
    , external "inst-lemma-dictionaries" (\ nm -> modifyLemmaT nm id instantiateDictsR id id :: TransformH Core ())
        [ "Instantiate all of the universally quantified dictionaries of the given lemma."
        , "Only works on dictionaries whose types are monomorphic (no free type variables)." ]
    , external "copy-lemma" (\ nm newName -> modifyLemmaT nm (const newName) idR id id :: TransformH Core ())
        [ "Copy a given lemma, with a new name." ]
    , external "modify-lemma" ((\ nm rr -> modifyLemmaT nm id (extractR rr) (const False) (const False)) :: LemmaName -> RewriteH QC -> TransformH Core ())
        [ "Modify a given lemma. Resets the proven status to Not Proven and used status to Not Used." ]
    , external "query-lemma" ((\ nm t -> getLemmaByNameT nm >>> arr lemmaQ >>> extractT t) :: LemmaName -> TransformH QC String -> TransformH Core String)
        [ "Apply a transformation to a lemma, returning the result." ]
    , external "show-lemma" ((\pp n -> showLemmaT n pp) :: PrettyPrinter -> LemmaName -> PrettyH Core)
        [ "Display a lemma." ]
    , external "show-lemmas" ((\pp n -> showLemmasT (Just n) pp) :: PrettyPrinter -> LemmaName -> PrettyH Core)
        [ "List lemmas whose names match search string." ]
    , external "show-lemmas" (showLemmasT Nothing :: PrettyPrinter -> PrettyH Core)
        [ "List lemmas." ]
    , external "extensionality" (promoteR . extensionalityR . Just :: String -> RewriteH QC)
        [ "Given a name 'x, then"
        , "f == g  ==>  forall x.  f x == g x" ]
    , external "extensionality" (promoteR (extensionalityR Nothing) :: RewriteH QC)
        [ "f == g  ==>  forall x.  f x == g x" ]
    , external "lhs" (promoteR . lhsR . core2qcR :: RewriteH Core -> RewriteH QC)
        [ "Apply a rewrite to the LHS of a quantified clause." ]
    , external "lhs" (promoteT . lhsT . core2qcT . extractT :: TransformH CoreTC String -> TransformH QC String)
        [ "Apply a transformation to the LHS of a quantified clause." ]
    , external "rhs" (promoteR . rhsR . core2qcR :: RewriteH Core -> RewriteH QC)
        [ "Apply a rewrite to the RHS of a quantified clause." ]
    , external "rhs" (promoteT . rhsT . core2qcT . extractT :: TransformH CoreTC String -> TransformH QC String)
        [ "Apply a transformation to the RHS of a quantified clause." ]
    , external "both" (promoteR . bothR . core2qcR :: RewriteH Core -> RewriteH QC)
        [ "Apply a rewrite to both sides of an equality, succeeding if either succeed." ]
    , external "both" ((\t -> do (r,s) <- promoteT (bothT (core2qcT (extractT t))); return (unlines [r,s])) :: TransformH CoreTC String -> TransformH QC String)
        [ "Apply a transformation to both sides of a quantified clause." ]
    ]

------------------------------------------------------------------------------

core2qcT :: forall c m a. Monad m => Transform c m Core a -> Transform c m QC a
core2qcT t = promoteT (extractT t :: Transform c m CoreExpr a)

core2qcR :: forall c m. Monad m => Rewrite c m Core -> Rewrite c m QC
core2qcR rr = promoteR (extractR rr :: Rewrite c m CoreExpr)

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

-- | @e@ ==> @let v = rhs in e@
eqRhsIntroR :: Quantified -> Rewrite c HermitM Core
eqRhsIntroR (Quantified bs (Equiv _ rhs)) = nonRecIntroR "rhs" (mkCoreLams bs rhs)

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

-- | Lift a transformation over 'QC' into a transformation over the left-hand side of a 'Quantified'.
lhsT :: (AddBindings c, ReadPath c Crumb, Monad m) => Transform c m QC a -> Transform c m Quantified a
lhsT t = quantifiedT successT (clauseT t successT (\_ l _ -> l)) (flip const)

-- | Lift a transformation over 'QC' into a transformation over the right-hand side of a 'Quantified'.
rhsT :: (AddBindings c, ReadPath c Crumb, Monad m) => Transform c m QC a -> Transform c m Quantified a
rhsT t = quantifiedT successT (clauseT successT t (\_ _ r -> r)) (flip const)

-- | Lift a transformation over 'QC' into a transformation over both sides of a 'Quantified'.
bothT :: (AddBindings c, ReadPath c Crumb, Monad m) => Transform c m QC a -> Transform c m Quantified (a, a)
bothT t = quantifiedT successT (clauseT t t (const (,))) (flip const)

-- | Lift a rewrite over 'QC' into a rewrite over the left-hand side of a 'Quantified'.
lhsR :: (AddBindings c, Monad m, ReadPath c Crumb) => Rewrite c m QC -> Rewrite c m Quantified
lhsR r = quantifiedR (clauseR r idR)

-- | Lift a rewrite over 'QC' into a rewrite over the right-hand side of a 'Quantified'.
rhsR :: (AddBindings c, Monad m, ReadPath c Crumb) => Rewrite c m QC -> Rewrite c m Quantified
rhsR r = quantifiedR (clauseR idR r)

-- | Lift a rewrite over 'QC' into a rewrite over both sides of a 'Quantified'.
bothR :: (AddBindings c, MonadCatch m, ReadPath c Crumb)
      => Rewrite c m QC -> Rewrite c m Quantified
bothR r = lhsR r >+> rhsR r

------------------------------------------------------------------------------

-- | Lift a transformation over 'Clause' into a transformation over a 'Quantified'.
quantifiedT :: (AddBindings c, Monad m, ReadPath c Crumb)
            => Transform c m [Var] a -> Transform c m Clause b -> (a -> b -> d) -> Transform c m Quantified d
quantifiedT tvs tc f = do
    Quantified vs cl <- idR
    f <$> (return vs >>> tvs) <*> (return cl >>> withVarsInScope vs tc)

quantifiedR :: (AddBindings c, ReadPath c Crumb, Monad m) => Rewrite c m Clause -> Rewrite c m Quantified
quantifiedR rr = quantifiedT idR rr Quantified

-- | Original clause passed to function so it can decide how to handle connective.
clauseT :: Monad m => Transform c m QC a -> Transform c m QC b -> (Clause -> a -> b -> d) -> Transform c m Clause d
clauseT t1 t2 f =
    readerT $ \ cl -> case cl of
        Conj  q1 q2 -> f cl <$> (return q1 >>> extractT t1) <*> (return q2 >>> extractT t2)
        Disj  q1 q2 -> f cl <$> (return q1 >>> extractT t1) <*> (return q2 >>> extractT t2)
        Impl  q1 q2 -> f cl <$> (return q1 >>> extractT t1) <*> (return q2 >>> extractT t2)
        Equiv e1 e2 -> f cl <$> (return e1 >>> extractT t1) <*> (return e2 >>> extractT t2)

clauseR :: Monad m => Rewrite c m QC -> Rewrite c m QC -> Rewrite c m Clause
clauseR r1 r2 =
    readerT $ \ cl -> case cl of
        Conj  q1 q2 -> Conj  <$> (return q1 >>> extractR r1) <*> (return q2 >>> extractR r2)
        Disj  q1 q2 -> Disj  <$> (return q1 >>> extractR r1) <*> (return q2 >>> extractR r2)
        Impl  q1 q2 -> Impl  <$> (return q1 >>> extractR r1) <*> (return q2 >>> extractR r2)
        Equiv q1 q2 -> Equiv <$> (return q1 >>> extractR r1) <*> (return q2 >>> extractR r2)

-- | Lift a transformation over '[Var]' into a transformation over the universally quantified variables of a 'Quantified'.
forallVarsT :: (AddBindings c, ReadPath c Crumb, Monad m) => Transform c m [Var] b -> Transform c m Quantified b
forallVarsT t = quantifiedT t successT const

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
    Lemma q p u <- idR
    qDoc <- return q >>> ppQuantifiedT pp
    let hDoc = PP.text (show nm) PP.<+> PP.text (if p then "(Proven)" else "(Not Proven)")
                                 PP.<+> PP.text (if u then "(Used)"   else "(Not Used)")
    return $ hDoc PP.$+$ PP.nest 2 qDoc

ppQuantifiedT :: PrettyPrinter -> PrettyH Quantified
ppQuantifiedT pp = do
    (d1,d2) <- quantifiedT (pForall pp) (ppClauseT pp) (,)
    return $ PP.sep [d1,d2]

ppClauseT :: PrettyPrinter -> PrettyH Clause
ppClauseT pp = do
    let t = promoteT (ppQuantifiedT pp) <+ promoteT (extractT (pCoreTC pp) :: PrettyH CoreExpr)
    (d1,d2,oper) <- clauseT t t (\ cl d1 d2 -> (d1,d2,  syntaxColor
                                                      $ PP.text
                                                      $ case cl of
                                                            Conj {}  -> "^"
                                                            Disj {}  -> "v"
                                                            Impl {}  -> "=>"
                                                            Equiv {} -> "="))

    return $ PP.sep [d1,oper,d2]

------------------------------------------------------------------------------

verifyQuantifiedT :: (AddBindings c, ReadPath c Crumb, MonadCatch m) => Transform c m Quantified ()
verifyQuantifiedT = quantifiedT successT verifyClauseT (flip const)

verifyClauseT :: (AddBindings c, ReadPath c Crumb, MonadCatch m) => Transform c m Clause ()
verifyClauseT =
    readerT (\case Conj  q1 q2 -> (return q1 >>> verifyQuantifiedT) >> (return q2 >>> verifyQuantifiedT)
                   Disj  q1 q2 -> (return q1 >>> verifyQuantifiedT) <+ (return q2 >>> verifyQuantifiedT)
                   Impl  _  _  -> fail "verifyClauseT: Impl TODO"
                   Equiv e1 e2 -> guardMsg (exprAlphaEq e1 e2) "the two sides of the equality do not match.")

-- TODO: doesn't catch lint errors in the quantifiers
lintQuantifiedT :: (AddBindings c, BoundVars c, ReadPath c Crumb, HasDynFlags m, MonadCatch m)
                => Transform c m Quantified String
lintQuantifiedT = quantifiedT successT lintClauseT (flip const)

lintClauseT :: (AddBindings c, BoundVars c, ReadPath c Crumb, HasDynFlags m, MonadCatch m) => Transform c m Clause String
lintClauseT = do
    let t = promoteT lintQuantifiedT <+ promoteT lintExprT
    (w1,w2) <- clauseT t t (const (,))
    return $ unlines [w1,w2]

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
retraction :: Maybe (RewriteH Core) -> CoreString -> CoreString -> BiRewriteH CoreExpr
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
    contextfreeT $ instantiateQuantified allDs

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
          go2 subst seen (Impl q1 q2) = do
            q1' <- go subst seen q1
            q2' <- go subst seen q2
            return $ Impl q1' q2'
          go2 subst _ (Equiv e1 e2) =
            let e1' = substExpr (text "unshadowQuantified e1") subst e1
                e2' = substExpr (text "unshadowQuantified e2") subst e2
            in return $ Equiv e1' e2'

inventNames :: UniqSet FastString -> FastString -> FastString
inventNames s nm = head [ nm' | i :: Int <- [0..]
                              , let nm' = nm `appendFS` (mkFastString (show i))
                              , not (nm' `elementOfUniqSet` s) ]

------------------------------------------------------------------------------

instantiateQuantifiedVarR :: (Var -> Bool) -> CoreString -> RewriteH Quantified
instantiateQuantifiedVarR p cs = prefixFailMsg "instantiation failed: " $ do
    bs <- forallVarsT idR
    (e,new) <- case filter p bs of
                [] -> fail "no universally quantified variables match predicate."
                (b:_) | isId b    -> let (before,_) = break (==b) bs
                                     in liftM (,[]) $ withVarsInScope before $ parseCoreExprT cs
                      | otherwise -> do let (before,_) = break (==b) bs
                                        (ty, tvs) <- withVarsInScope before $ parseTypeWithHolesT cs
                                        return (Type ty, tvs)
    contextfreeT (instantiateQuantifiedVar p e new) >>> (lintQuantifiedT >> idR) -- lint for sanity

------------------------------------------------------------------------------

getLemmasT :: HasLemmas m => Transform c m x Lemmas
getLemmasT = constT getLemmas

getLemmaByNameT :: (HasLemmas m, Monad m) => LemmaName -> Transform c m x Lemma
getLemmaByNameT nm = getLemmasT >>= maybe (fail $ "No lemma named: " ++ show nm) return . Map.lookup nm

lemmaR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
          , HasLemmas m, MonadCatch m, MonadUnique m)
       => LemmaName -> BiRewrite c m CoreExpr
lemmaR nm = afterBiR (beforeBiR (getLemmaByNameT nm) (birewrite . lemmaQ)) (markLemmaUsedT nm >> idR)

------------------------------------------------------------------------------

insertLemmaT :: (HasLemmas m, Monad m) => LemmaName -> Lemma -> Transform c m a ()
insertLemmaT nm l = constT $ insertLemma nm l

insertLemmasT :: (HasLemmas m, Monad m) => [NamedLemma] -> Transform c m a ()
insertLemmasT = constT . mapM_ (uncurry insertLemma)

modifyLemmaT :: (HasLemmas m, Monad m)
             => LemmaName
             -> (LemmaName -> LemmaName) -- ^ modify lemma name
             -> Rewrite c m Quantified   -- ^ rewrite the quantified clause
             -> (Bool -> Bool)           -- ^ modify proven status
             -> (Bool -> Bool)           -- ^ modify used status
             -> Transform c m a ()
modifyLemmaT nm nFn rr pFn uFn = do
    Lemma q p u <- getLemmaByNameT nm
    q' <- rr <<< return q
    constT $ insertLemma (nFn nm) $ Lemma q' (pFn p) (uFn u)

markLemmaUsedT :: (HasLemmas m, Monad m) => LemmaName -> Transform c m a ()
markLemmaUsedT nm = modifyLemmaT nm id idR id (const True)

markLemmaProvedT :: (HasLemmas m, Monad m) => LemmaName -> Transform c m a ()
markLemmaProvedT nm = modifyLemmaT nm id idR (const True) id
------------------------------------------------------------------------------

lemmaNameToQuantifiedT :: (HasLemmas m, Monad m) => LemmaName -> Transform c m x Quantified
lemmaNameToQuantifiedT nm = liftM lemmaQ $ getLemmaByNameT nm

-- | @e@ ==> @let v = lhs in e@  (also works in a similar manner at Program nodes)
lemmaLhsIntroR :: LemmaName -> RewriteH Core
lemmaLhsIntroR = lemmaNameToQuantifiedT >=> eqLhsIntroR

-- | @e@ ==> @let v = rhs in e@  (also works in a similar manner at Program nodes)
lemmaRhsIntroR :: LemmaName -> RewriteH Core
lemmaRhsIntroR = lemmaNameToQuantifiedT >=> eqRhsIntroR

------------------------------------------------------------------------------
