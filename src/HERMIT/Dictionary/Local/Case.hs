{-# LANGUAGE CPP, MultiWayIf, LambdaCase, ScopedTypeVariables, FlexibleContexts, TupleSections #-}

module HERMIT.Dictionary.Local.Case
    ( -- * Rewrites on Case Expressions
      externals
    , caseFloatAppR
    , caseFloatArgR
    , caseFloatCaseR
    , caseFloatCastR
    , caseFloatLetR
    , caseFloatR
    , caseFloatInR
    , caseFloatInAppR
    , caseFloatInArgsR
    , caseReduceR
    , caseReduceDataconR
    , caseReduceLiteralR
    , caseReduceIdR
    , caseSplitR
    , caseSplitInlineR
    , caseInlineScrutineeR
    , caseInlineAlternativeR
    , caseMergeAltsR
    , caseMergeAltsWithBinderR
    , caseElimR
    , caseElimInlineScrutineeR
    , caseElimMergeAltsR
    , caseIntroSeqR
    , caseElimSeqR
    )
where

import Data.List
import Data.Monoid
import Control.Arrow
import Control.Applicative

import HERMIT.Core
import HERMIT.Context
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.GHC
import HERMIT.External
import HERMIT.Utilities
import HERMIT.ParserCore

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Inline hiding (externals)
import HERMIT.Dictionary.AlphaConversion hiding (externals)
import HERMIT.Dictionary.Fold (foldVarR)
import HERMIT.Dictionary.GHC (substCoreExpr)
import HERMIT.Dictionary.Undefined (verifyStrictT)

-- NOTE: these are hard to test in small examples, as GHC does them for us, so use with caution
------------------------------------------------------------------------------

-- | Externals relating to Case expressions.
externals :: [External]
externals =
    [ external "case-float-app" (promoteExprR caseFloatAppR :: RewriteH Core)
        [ "(case ec of alt -> e) v ==> case ec of alt -> e v" ]              .+ Commute .+ Shallow
    , external "case-float-arg" ((\ strict -> promoteExprR (caseFloatArg Nothing (Just strict))) :: RewriteH Core -> RewriteH Core)
        [ "Given a proof that f is strict, then"
        , "f (case s of alt -> e) ==> case s of alt -> f e" ]                .+ Commute .+ Shallow
    , external "case-float-arg" ((\ f strict -> promoteExprR (caseFloatArg (Just f) (Just strict))) :: CoreString -> RewriteH Core -> RewriteH Core)
        [ "For a specified f, given a proof that f is strict, then"
        , "f (case s of alt -> e) ==> case s of alt -> f e" ]                .+ Commute .+ Shallow
    , external "case-float-arg-unsafe" ((\ f -> promoteExprR (caseFloatArg (Just f) Nothing)) :: CoreString -> RewriteH Core)
        [ "For a specified f,"
        , "f (case s of alt -> e) ==> case s of alt -> f e" ]                .+ Commute .+ Shallow .+ PreCondition
    , external "case-float-arg-unsafe" (promoteExprR (caseFloatArg Nothing Nothing) :: RewriteH Core)
        [ "f (case s of alt -> e) ==> case s of alt -> f e" ]                .+ Commute .+ Shallow .+ PreCondition
    , external "case-float-case" (promoteExprR caseFloatCaseR :: RewriteH Core)
        [ "case (case ec of alt1 -> e1) of alta -> ea ==> case ec of alt1 -> case e1 of alta -> ea" ] .+ Commute .+ Eval
    , external "case-float-cast" (promoteExprR caseFloatCastR :: RewriteH Core)
        [ "cast (case s of p -> e) co ==> case s of p -> cast e co" ]        .+ Shallow .+ Commute
    , external "case-float-let" (promoteExprR caseFloatLetR :: RewriteH Core)
        [ "let v = case ec of alt1 -> e1 in e ==> case ec of alt1 -> let v = e1 in e" ] .+ Commute .+ Shallow
    , external "case-float" (promoteExprR caseFloatR :: RewriteH Core)
        [ "case-float = case-float-app <+ case-float-case <+ case-float-let <+ case-float-cast" ]    .+ Commute .+ Shallow
    , external "case-float-in" (promoteExprR caseFloatInR :: RewriteH Core)
        [ "Float in a Case whatever the context." ]                             .+ Commute .+ Shallow .+ PreCondition
    , external "case-float-in-args" (promoteExprR caseFloatInArgsR :: RewriteH Core)
        [ "Float in a Case whose alternatives are parallel applications of the same function." ] .+ Commute .+ Shallow .+ PreCondition
    -- , external "case-float-in-app" (promoteExprR caseFloatInApp :: RewriteH Core)
    --     [ "Float in a Case whose alternatives are applications of different functions with the same arguments." ] .+ Commute .+ Shallow .+ PreCondition
    , external "case-reduce" (promoteExprR (caseReduceR True) :: RewriteH Core)
        [ "Case of Known Constructor"
        , "case-reduce-datacon <+ case-reduce-literal" ]                     .+ Shallow .+ Eval
    , external "case-reduce-datacon" (promoteExprR (caseReduceDataconR True) :: RewriteH Core)
        [ "Case of Known Constructor"
        , "case C v1..vn of C w1..wn -> e ==> let { w1 = v1 ; .. ; wn = vn } in e" ]    .+ Shallow .+ Eval
    , external "case-reduce-literal" (promoteExprR (caseReduceLiteralR True) :: RewriteH Core)
        [ "Case of Known Constructor"
        , "case L of L -> e ==> e" ]                                         .+ Shallow .+ Eval
    , external "case-reduce-id" (promoteExprR (caseReduceIdR True) :: RewriteH Core)
        [ "Inline the case scrutinee (if it is an identifier) and then case-reduce." ] .+ Shallow .+ Eval .+ Context
    , external "case-split" (promoteExprR . caseSplitR . cmpString2Var :: String -> RewriteH Core)
        [ "case-split 'x"
        , "e ==> case x of C1 vs -> e; C2 vs -> e, where x is free in e" ] .+ Shallow
    , external "case-split-inline" (promoteExprR . caseSplitInlineR . cmpString2Var :: String -> RewriteH Core)
        [ "Like case-split, but additionally inlines the matched constructor "
        , "applications for all occurances of the named variable." ] .+ Deep
    , external "case-intro-seq" (promoteExprR . caseIntroSeqR . cmpString2Var :: String -> RewriteH Core)
        [ "Force evaluation of a variable by introducing a case."
        , "case-seq 'v is is equivalent to adding @(seq v)@ in the source code." ] .+ Shallow .+ Introduce
    , external "case-elim-seq" (promoteExprR caseElimSeqR :: RewriteH Core)
        [ "Eliminate a case that corresponds to a pointless seq."  ] .+ Deep .+ Eval
    , external "case-inline-alternative" (promoteExprR caseInlineAlternativeR :: RewriteH Core)
        [ "Inline the case binder as the case-alternative pattern everywhere in the case alternatives." ] .+ Deep
    , external "case-inline-scrutinee" (promoteExprR caseInlineScrutineeR :: RewriteH Core)
        [ "Inline the case binder as the case scrutinee everywhere in the case alternatives." ] .+ Deep
    , external "case-merge-alts" (promoteExprR caseMergeAltsR :: RewriteH Core)
        [ "Merge all case alternatives into a single default case."
        , "The RHS of each alternative must be the same."
        , "case s of {pat1 -> e ; pat2 -> e ; ... ; patn -> e} ==> case s of {_ -> e}" ]
    , external "case-merge-alts-with-binder" (promoteExprR caseMergeAltsWithBinderR :: RewriteH Core)
        [ "A cleverer version of 'mergeCaseAlts' that first attempts to"
        , "abstract out any occurrences of the alternative pattern using the case binder." ] .+ Deep
    , external "case-elim" (promoteExprR caseElimR :: RewriteH Core)
        [ "case s of w; C vs -> e ==> e if w and vs are not free in e" ]     .+ Shallow
    , external "case-elim-inline-scrutinee" (promoteExprR caseElimInlineScrutineeR :: RewriteH Core)
        [ "Eliminate a case, inlining any occurrences of the case binder as the scrutinee." ] .+ Deep
    , external "case-elim-merge-alts" (promoteExprR caseElimMergeAltsR :: RewriteH Core)
        [ "Eliminate a case, merging the case alternatives into a single default alternative",
          "and inlining the case binder as the scrutinee (if possible)." ] .+ Deep
    , external "case-fold-binder" (promoteExprR caseFoldBinderR :: RewriteH Core)
        [ "In the case alternatives, fold any occurrences of the case alt patterns to the case binder." ]
    ]

------------------------------------------------------------------------------

-- | case s of w; C vs -> e ==> e if w and vs are not free in e
caseElimR :: Rewrite c HermitM CoreExpr
caseElimR = prefixFailMsg "Case elimination failed: " $
            withPatFailMsg (wrongExprForm "Case s bnd ty alts") $
 do Case _ bnd _ alts <- idR
    case alts of
        [(_, vs, e)] -> do let fvs = freeVarsExpr e
                           guardMsg (isEmptyVarSet $ intersectVarSet (mkVarSet (bnd:vs)) fvs) "case binder or pattern binders free in RHS."
                           return e
        _ -> fail "more than one case alternative."

------------------------------------------------------------------------------

-- | (case s of alt1 -> e1; alt2 -> e2) v ==> case s of alt1 -> e1 v; alt2 -> e2 v
caseFloatAppR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatAppR = prefixFailMsg "Case floating from App function failed: " $
  do
    captures    <- appT (map mkVarSet <$> caseAltVarsT) (arr freeVarsExpr) (flip (map . intersectVarSet))
    bndrCapture <- appT caseBinderIdT (arr freeVarsExpr) elemVarSet
    appT ((if not bndrCapture then idR else alphaCaseBinderR Nothing)
          >>> caseAllR idR idR idR (\i -> if isEmptyVarSet (captures !! i) then idR else alphaAltR)
         )
          idR
          (\(Case s b _ alts) v -> let newAlts = mapAlts (`App` v) alts
                                    in Case s b (coreAltsType newAlts) newAlts)

caseFloatArg :: Maybe CoreString -> Maybe (RewriteH Core) -> RewriteH CoreExpr
caseFloatArg mfstr mstrictCore = let mstrict = extractR <$> mstrictCore
                                  in case mfstr of
                                       Nothing    -> caseFloatArgR Nothing mstrict
                                       Just f_str -> do f <- parseCoreExprT f_str
                                                        caseFloatArgR (Just f) mstrict

-- | @f (case s of alt1 -> e1; alt2 -> e2)@ ==> @case s of alt1 -> f e1; alt2 -> f e2@
--   Only safe if @f@ is strict.
caseFloatArgR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c)
              => Maybe CoreExpr -> Maybe (Rewrite c HermitM CoreExpr) -- ^ Maybe the function to float past, and maybe a proof of its strictness.
              -> Rewrite c HermitM CoreExpr
caseFloatArgR mf mstrict = prefixFailMsg "Case floating from App argument failed: " $
                           withPatFailMsg "App f (Case s w ty alts)" $
  do App f (Case s w _ alts) <- idR

     whenJust (\ f' -> guardMsg (exprAlphaEq f f') "given function does not match current application.") mf
     whenJust (verifyStrictT f) mstrict

     let fvs         = freeVarsExpr f
         altCaptures = map (intersectVarSet fvs . mkVarSet . altVars) alts
         bndrCapture = elemVarSet w fvs

     if | bndrCapture                   -> appAllR idR (alphaCaseBinderR Nothing) >>> caseFloatArgR Nothing Nothing
        | all isEmptyVarSet altCaptures -> let new_alts = mapAlts (App f) alts
                                            in return $ Case s w (coreAltsType new_alts) new_alts
        | otherwise                     -> appAllR idR (caseAllR idR idR idR (\ n -> let vs = varSetElems (altCaptures !! n)
                                                                                      in if null vs then idR else alphaAltVarsR vs
                                                                             )
                                                       ) >>> caseFloatArgR Nothing Nothing

-- caseFloatArgR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, BoundVars c, HasGlobalRdrEnv c)
--               => Maybe (CoreExpr, Maybe (Rewrite c HermitM CoreExpr)) -- ^ Maybe the function to float past, and maybe a proof of its strictness.
--               -> Rewrite c HermitM CoreExpr
-- caseFloatArgR mfstrict = prefixFailMsg "Case floating from App argument failed: " $
--                          withPatFailMsg "App f (Case s w ty alts)" $
--   do App f (Case s w _ alts) <- idR
--      whenJust (\ (f', mstrict) ->
--                      do guardMsg (exprAlphaEq f f') "given function does not match current application."
--                         whenJust (verifyStrictT f) mstrict
--               )
--               mfstrict

--      let fvs         = freeVarsExpr f
--          altCaptures = map (intersectVarSet fvs . mkVarSet . altVars) alts
--          bndrCapture = elemVarSet w fvs

--      if | bndrCapture                   -> appAllR idR (alphaCaseBinderR Nothing) >>> caseFloatArgR Nothing
--         | all isEmptyVarSet altCaptures -> let new_alts = mapAlts (App f) alts
--                                             in return $ Case s w (coreAltsType new_alts) new_alts
--         | otherwise                     -> appAllR idR (caseAllR idR idR idR (\ n -> let vs = varSetElems (altCaptures !! n)
--                                                                                       in if null vs then idR else alphaAltVarsR vs
--                                                                              )
--                                                        ) >>> caseFloatArgR Nothing

-- | case (case s1 of alt11 -> e11; alt12 -> e12) of alt21 -> e21; alt22 -> e22
--   ==>
--   case s1 of
--     alt11 -> case e11 of alt21 -> e21; alt22 -> e22
--     alt12 -> case e12 of alt21 -> e21; alt22 -> e22
caseFloatCaseR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatCaseR = prefixFailMsg "Case floating from Case failed: " $
  do
    captures <- caseT (map mkVarSet <$> caseAltVarsT) idR mempty (const $ arr freeVarsAlt) (\ vss w () fvs -> map (intersectVarSet (delVarSet (unionVarSets fvs) w)) vss)
    -- does the binder of the inner case, shadow a free variable in any of the outer case alts?
    bndrCapture <- caseT caseBinderIdT idR mempty (const $ arr freeVarsAlt) (\ innerBndr w () fvs -> innerBndr `elemVarSet` (delVarSet (unionVarSets fvs) w))
    caseT ((if not bndrCapture then idR else alphaCaseBinderR Nothing)
           >>> caseAllR idR idR idR (\i -> if isEmptyVarSet (captures !! i) then idR else alphaAltR)
          )
          idR
          idR
          (const idR)
          (\ (Case s1 b1 _ alts1) b2 ty alts2 -> Case s1 b1 ty $ mapAlts (\s -> Case s b2 ty alts2) alts1)

-- | let v = case s of alt1 -> e1 in e ==> case s of alt1 -> let v = e1 in e
caseFloatLetR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatLetR = prefixFailMsg "Case floating from Let failed: " $
  do vs <- letNonRecT idR caseAltVarsT mempty (\ letVar caseVars () -> letVar `elem` concat caseVars)
     let bdsAction = if not vs then idR else nonRecAllR idR alphaCaseR
     letT bdsAction idR $ \ (NonRec v (Case s b _ alts)) e -> let newAlts = mapAlts (\ rhs -> Let (NonRec v rhs) e) alts
                                                               in Case s b (coreAltsType newAlts) newAlts

-- | cast (case s of p -> e) co ==> case s of p -> cast e co
caseFloatCastR :: MonadCatch m => Rewrite c m CoreExpr
caseFloatCastR = prefixFailMsg "Case float from cast failed: " $
                withPatFailMsg (wrongExprForm "Cast (Case s bnd ty alts) co") $
    do Cast (Case s bnd _ alts) co <- idR
       let alts' = mapAlts (flip Cast co) alts
       return $ Case s bnd (coreAltsType alts') alts'

-- | caseFloatR = caseFloatAppR <+ caseFloatCaseR <+ caseFloatLetR <+ caseFloatCastR
--   Note: does NOT include caseFloatArg
caseFloatR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatR = setFailMsg "Unsuitable expression for Case floating." $
    caseFloatAppR <+ caseFloatCaseR <+ caseFloatLetR <+ caseFloatCastR

------------------------------------------------------------------------------

-- | Float in a Case whatever the context.
caseFloatInR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
caseFloatInR = setFailMsg "Case floating in failed." $
    caseFloatInAppR <+ caseFloatInArgsR

-- | Unimplemented!
caseFloatInAppR :: Monad m => Rewrite c m CoreExpr
caseFloatInAppR = fail "caseFloatInApp: TODO"

caseFloatInArgsR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
caseFloatInArgsR = prefixFailMsg "Case floating into arguments failed: " $
                   withPatFailMsg (wrongExprForm "Case s v t alts") $
    do Case s bndr _ty alts <- idR
       (vss, fs, argss) <- caseT mempty mempty mempty (\ _ -> altT mempty (\ _ -> idR) callT $ \ () vs (fn, args) -> (vs, fn, args))
                                                      (\ () () () alts' -> unzip3 [ (bndr:vs, fn, args) | (vs,fn,args) <- alts' ])
       guardMsg (equivalentBy exprAlphaEq fs) "alternatives are not parallel in function call."
       let fvs = [ varSetElems $ unionVarSets $ map freeVarsExpr $ f:tyArgs
                 | (f,args) <- zip fs argss
                 , let tyArgs = takeWhile isTyCoArg args ] -- pattern binders can be existential types
       guardMsg (all null $ zipWith intersect fvs vss) "function bound by case binders."
       let argss' = transpose argss
       guardMsg (all (equivalentBy exprAlphaEq) $ filter (isTyCoArg . head) argss') "function applied at different types."
       return $ mkCoreApps (head fs) [ if isTyCoArg (head args)
                                       then head args
                                       else let alts' = [ (ac, vs, arg) | ((ac,vs,_),arg) <- zip alts args ]
                                            in Case s bndr (coreAltsType alts') alts'
                                     | args <- argss' ]

------------------------------------------------------------------------------

-- | Inline the case scrutinee (if it is an identifier), and then perform case reduction.
--   If first argument is True, perform substitution in RHS, if False, build let expressions.
caseReduceIdR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Bool -> Rewrite c HermitM CoreExpr
caseReduceIdR subst = caseAllR inlineR idR idR (const idR) >>> caseReduceR subst

-- | Case of Known Constructor.
--   Eliminate a case if the scrutinee is a data constructor or a literal.
--   If first argument is True, perform substitution in RHS, if False, build let expressions.
caseReduceR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Bool -> Rewrite c HermitM CoreExpr
caseReduceR subst =
    setFailMsg "Unsuitable expression for Case reduction." $
    caseReduceDataconR subst <+ caseReduceLiteralR subst

-- | Case of Known Constructor.
--   Eliminate a case if the scrutinee is a literal.
--   If first argument is True, perform substitution in RHS, if False, build let expressions.
-- NB: LitAlt cases don't do evaluation
caseReduceLiteralR :: MonadCatch m => Bool -> Rewrite c m CoreExpr
caseReduceLiteralR subst =
    prefixFailMsg "Case reduction failed: " $
    withPatFailMsg (wrongExprForm "Case (Lit l) v t alts") $ do
        Case s bndr _ alts <- idR
#if __GLASGOW_HASKELL__ > 706
        let in_scope = mkInScopeSet (localFreeVarsExpr s)
        case exprIsLiteral_maybe (in_scope, idUnfolding) s of
#else
        case exprIsLiteral_maybe idUnfolding s of
#endif
            Nothing -> fail "scrutinee is not a literal."
            Just l  -> do guardMsg (not (litIsLifted l)) "cannot case-reduce lifted literals" -- see Trac #5603
                          case findAlt (LitAlt l) alts of
                            Nothing          -> fail "no matching alternative."
                            Just (_, _, rhs) -> return $ if subst
                                                         then substCoreExpr bndr (Lit l) rhs
                                                         else mkCoreLet (NonRec bndr (Lit l)) rhs

-- | Case of Known Constructor.
--   Eliminate a case if the scrutinee is a data constructor.
--   If first argument is True, perform substitution in RHS, if False, build let expressions.
caseReduceDataconR :: forall c. (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Bool -> Rewrite c HermitM CoreExpr
caseReduceDataconR subst = prefixFailMsg "Case reduction failed: " $
                           withPatFailMsg (wrongExprForm "Case e v t alts") go
    where
        go :: Rewrite c HermitM CoreExpr
        go = do
            Case e bndr _ alts <- idR
#if __GLASGOW_HASKELL__ > 706
            let in_scope = mkInScopeSet (localFreeVarsExpr e)
            case exprIsConApp_maybe (in_scope, idUnfolding) e of
#else
            case exprIsConApp_maybe idUnfolding e of
#endif
                Nothing                -> fail "head of scrutinee is not a data constructor."
                Just (dc, univTys, es) -> case findAlt (DataAlt dc) alts of
                    Nothing             -> fail "no matching alternative."
                    Just (dc', vs, rhs) -> -- dc' is either DEFAULT or dc
                        -- NB: It is possible that es contains one or more existentially quantified types.
                        let fvss    = map freeVarsExpr $ map Type univTys ++ es
                            shadows = [ v | (v,n) <- zip vs [1..], any (elemVarSet v) (drop n fvss) ]
                        in if | any (elemVarSet bndr) fvss -> alphaCaseBinderR Nothing >>> go
                              | null shadows               -> do let binds = zip (bndr : vs) (e : es)
                                                                 return $ if subst
                                                                          then foldr (uncurry substCoreExpr) rhs binds
                                                                          else flip mkCoreLets rhs $ map (uncurry NonRec) binds
                              | otherwise                  -> caseOneR (fail "scrutinee") (fail "binder") (fail "type") (\ _ -> acceptR (\ (dc'',_,_) -> dc'' == dc') >>> alphaAltVarsR shadows) >>> go
-- WARNING: The alpha-renaming to avoid variable capture has not been tested.  We need testing infrastructure!

-- | Case split a free identifier in an expression:
--
-- E.g. Assume expression e which mentions i :: [a]
--
-- e ==> case i of i
--         []     -> e
--         (a:as) -> e
caseSplitR :: (Id -> Bool) -> Rewrite c HermitM CoreExpr
caseSplitR idPred = prefixFailMsg "caseSplit failed: " $
               do i            <- matchingFreeIdT idPred
                  (tycon, tys) <- splitTyConAppM (idType i)
                  let aNms     = map (:[]) $ cycle ['a'..'z']
                  contextfreeT $ \ e -> do dcsAndVars <- mapM (\ dc -> (dc,) <$> sequence [ newIdH a ty | (a,ty) <- zip aNms $ dataConInstArgTys dc tys ])
                                                              (tyConDataCons tycon)
                                           w <- cloneVarH (++ "'") i
                                           let e' = substCoreExpr i (Var w) e
                                               alts = [ (DataAlt dc, as, e') | (dc,as) <- dcsAndVars ]
                                           return $ Case (Var i) w (coreAltsType alts) alts

-- | Force evaluation of an identifier by introducing a case.
--   This is equivalent to adding @(seq v)@ in the source code.
--
-- e -> case v of v
--        _ -> e
caseIntroSeqR :: (Id -> Bool) -> Rewrite c HermitM CoreExpr
caseIntroSeqR idPred = prefixFailMsg "case-intro-seq failed: " $
             do i <- matchingFreeIdT idPred
                contextfreeT $ \ e -> do guardMsg (not $ isTyCoArg e) "cannot case on a type or coercion."
                                         w <- cloneVarH (++ "'") i
                                         let e' = substCoreExpr i (Var w) e
                                             alts = [(DEFAULT, [], e')]
                                         return $ Case (Var i) w (coreAltsType alts) alts

-- auxillary function for use by caseSplit and caseSeq
matchingFreeIdT :: Monad m => (Id -> Bool) -> Translate c m CoreExpr Id
matchingFreeIdT idPred = do
  fvs <- arr freeVarsExpr
  case varSetElems (filterVarSet (\ v -> idPred v && isId v) fvs) of
    []    -> fail "provided name is not a free identifier."
    [i]   -> return i
    is    -> fail ("provided name matches " ++ show (length is) ++ " free identifiers.")

-- | Like caseSplit, but additionally inlines the constructor applications
-- for each occurance of the named variable.
--
-- > caseSplitInline idPred = caseSplit idPred >>> caseInlineAlternativeR
caseSplitInlineR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => (Id -> Bool) -> Rewrite c HermitM CoreExpr
caseSplitInlineR idPred = caseSplitR idPred >>> caseInlineAlternativeR

------------------------------------------------------------------------------

caseInlineBinderR :: forall c. (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => CaseBinderInlineOption -> Rewrite c HermitM CoreExpr
caseInlineBinderR opt =
  do w <- caseBinderIdT
     caseAllR idR idR idR $ \ _ -> setFailMsg "no inlinable occurrences." $
                                   do depth <- varBindingDepthT w
                                      extractR $ anybuR (promoteExprR (configurableInlineR (CaseBinderOnly opt) (varIsOccurrenceOfT w depth)) :: Rewrite c HermitM Core)

-- | Inline the case binder as the case scrutinee everywhere in the case alternatives.
caseInlineScrutineeR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseInlineScrutineeR = prefixFailMsg "case-inline-scrutinee failed: " $
                       caseInlineBinderR Scrutinee

-- | Inline the case binder as the case-alternative pattern everywhere in the case alternatives.
caseInlineAlternativeR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseInlineAlternativeR = prefixFailMsg "case-inline-alternative failed: " $
                         caseInlineBinderR Alternative

------------------------------------------------------------------------------

-- | Merge all case alternatives into a single default case.
--   The RHS of each alternative must be the same.
--   @case s of {pat1 -> e ; pat2 -> e ; ... ; patn -> e}@ ==> @case s of {_ -> e}@
caseMergeAltsR :: MonadCatch m => Rewrite c m CoreExpr
caseMergeAltsR = prefixFailMsg "merge-case-alts failed: " $
                 withPatFailMsg (wrongExprForm "Case e w ty alts") $
                 do Case e w ty alts <- idR
                    guardMsg (notNull alts) "zero alternatives cannot be merged."
                    let rhss = [ rhs | (_,_,rhs) <- alts ]
                    guardMsg (equivalentBy exprAlphaEq rhss) "right-hand sides are not all equal."
                    guardMsg (all altVarsUnused alts) "variables bound in case alt pattern appear free in alt right-hand side."
                    return $ Case e w ty [(DEFAULT,[],head rhss)]

-- | In the case alternatives, fold any occurrences of the case alt patterns to the case binder.
caseFoldBinderR :: forall c.  (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFoldBinderR = prefixFailMsg "case-fold-binder failed: " $ do
    w <- caseBinderIdT
    caseAllR idR idR idR $ \ _ -> do depth <- varBindingDepthT w
                                     extractR $ anybuR (promoteExprR (foldVarR w (Just depth)) :: Rewrite c HermitM Core)

-- | A cleverer version of 'mergeCaseAlts' that first attempts to abstract out any occurrences of the alternative pattern using the case binder.
caseMergeAltsWithBinderR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseMergeAltsWithBinderR =
    prefixFailMsg "merge-case-alts-with-binder failed: " $
    withPatFailMsg (wrongExprForm "Case e w ty alts") $
    tryR caseFoldBinderR >>> caseMergeAltsR

-- | Eliminate a case, inlining any occurrences of the case binder as the scrutinee.
caseElimInlineScrutineeR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseElimInlineScrutineeR = alphaCaseBinderR Nothing >>> tryR caseInlineScrutineeR >>> caseElimR

-- | Eliminate a case, merging the case alternatives into a single default alternative and inlining the case binder as the scrutinee (if possible).
caseElimMergeAltsR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseElimMergeAltsR = tryR caseFoldBinderR >>> tryR caseMergeAltsR >>> caseElimInlineScrutineeR

------------------------------------------------------------------------------

-- | Eliminate a case that corresponds to a pointless 'seq'.
caseElimSeqR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseElimSeqR = prefixFailMsg "case-elim-seq failed: " $
               withPatFailMsg "not a seq case." $
  do Case s w _ [(DEFAULT,[],rhs)] <- idR

     let is = case s of
                Var i -> [i,w]
                _     -> [w]

     if is `isForcedIn` rhs
       then caseElimInlineScrutineeR
       else fail "cannot be sure that this seq case is pointless.  Use case-elim-inline-scrutinee if you want to proceed anyway."

-- | Will forcing the expression to WHNF always force one of the given identifiers?
isForcedIn :: [Id] -> CoreExpr -> Bool
isForcedIn is = \case
                   Var i         -> i `elem` is
                   App f _       -> is `isForcedIn` f
                   Let _ body    -> is `isForcedIn` body
                   Case s _ _ _  -> is `isForcedIn` s
                   Cast e _      -> is `isForcedIn` e
                   Tick _ e      -> is `isForcedIn` e
                   _             -> False

------------------------------------------------------------------------------

altVarsUnused :: CoreAlt -> Bool
altVarsUnused (_,vs,rhs) = all (`notElemVarSet` freeVarsExpr rhs) vs

------------------------------------------------------------------------------
