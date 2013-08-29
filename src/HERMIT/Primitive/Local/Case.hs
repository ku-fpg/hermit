{-# LANGUAGE CPP, MultiWayIf, ScopedTypeVariables, FlexibleContexts, TupleSections #-}

module HERMIT.Primitive.Local.Case
    ( -- * Rewrites on Case Expressions
      externals
    , caseFloatAppR
    , caseFloatArgR
    , caseFloatCaseR
    , caseFloatCastR
    , caseFloatLetR
    , caseFloatR
    , caseUnfloatR
    , caseUnfloatAppR
    , caseUnfloatArgsR
    , caseReduceR
    , caseReduceDataconR
    , caseReduceLiteralR
    , caseSplitR
    , caseSplitInlineR
    , caseInlineScrutineeR
    , caseInlineAlternativeR
    , caseMergeAltsR
    , caseMergeAltsWithWildR
    , caseElimR
    , caseElimInlineScrutineeR
    , caseElimMergeAltsR
    ) where

import GhcPlugins

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

import HERMIT.Primitive.Common
import HERMIT.Primitive.GHC hiding (externals)
import HERMIT.Primitive.Inline hiding (externals)
import HERMIT.Primitive.AlphaConversion hiding (externals)
import HERMIT.Primitive.Fold (foldVarR)

import qualified Language.Haskell.TH as TH

-- NOTE: these are hard to test in small examples, as GHC does them for us, so use with caution
------------------------------------------------------------------------------

-- | Externals relating to Case expressions.
externals :: [External]
externals =
    [ external "case-float-app" (promoteExprR caseFloatAppR :: RewriteH Core)
        [ "(case ec of alt -> e) v ==> case ec of alt -> e v" ]              .+ Commute .+ Shallow .+ Bash
    , external "case-float-arg" (promoteExprR caseFloatArgR :: RewriteH Core)
        [ "f (case s of alt -> e) ==> case s of alt -> f e" ]                .+ Commute .+ Shallow .+ PreCondition
    , external "case-float-case" (promoteExprR caseFloatCaseR :: RewriteH Core)
        [ "case (case ec of alt1 -> e1) of alta -> ea ==> case ec of alt1 -> case e1 of alta -> ea" ] .+ Commute .+ Eval .+ Bash
    , external "case-float-cast" (promoteExprR caseFloatCastR :: RewriteH Core)
        [ "cast (case s of p -> e) co ==> case s of p -> cast e co" ]        .+ Shallow .+ Commute .+ Bash
    , external "case-float-let" (promoteExprR caseFloatLetR :: RewriteH Core)
        [ "let v = case ec of alt1 -> e1 in e ==> case ec of alt1 -> let v = e1 in e" ] .+ Commute .+ Shallow .+ Bash
    , external "case-float" (promoteExprR caseFloatR :: RewriteH Core)
        [ "Float a Case whatever the context." ]                             .+ Commute .+ Shallow .+ PreCondition
    , external "case-unfloat" (promoteExprR caseUnfloatR :: RewriteH Core)
        [ "Unfloat a Case whatever the context." ]                             .+ Commute .+ Shallow .+ PreCondition
    , external "case-unfloat-args" (promoteExprR caseUnfloatArgsR :: RewriteH Core)
        [ "Unfloat a Case whose alternatives are parallel applications of the same function." ] .+ Commute .+ Shallow .+ PreCondition
    -- , external "case-unfloat-app" (promoteExprR caseUnfloatApp :: RewriteH Core)
    --     [ "Unfloat a Case whole alternatives are applications of different functions with the same arguments." ] .+ Commute .+ Shallow .+ PreCondition
    , external "case-reduce" (promoteExprR caseReduceR :: RewriteH Core)
        [ "case-reduce-datacon <+ case-reduce-literal" ]                     .+ Shallow .+ Eval .+ Bash
    , external "case-reduce-datacon" (promoteExprR caseReduceDataconR :: RewriteH Core)
        [ "case-of-known-constructor"
        , "case C v1..vn of C w1..wn -> e ==> let { w1 = v1 ; .. ; wn = vn } in e" ]    .+ Shallow .+ Eval
    , external "case-reduce-literal" (promoteExprR caseReduceLiteralR :: RewriteH Core)
        [ "case L of L -> e ==> e" ]                                         .+ Shallow .+ Eval
    , external "case-split" (promoteExprR . caseSplitR :: TH.Name -> RewriteH Core)
        [ "case-split 'x"
        , "e ==> case x of C1 vs -> e; C2 vs -> e, where x is free in e" ] .+ Shallow
    , external "case-split-inline" (caseSplitInlineR :: TH.Name -> RewriteH Core)
        [ "Like case-split, but additionally inlines the matched constructor "
        , "applications for all occurances of the named variable." ] .+ Deep
    , external "case-seq" (promoteExprR . caseSeqR :: TH.Name -> RewriteH Core)
        [ "Force evaluation of a variable by introducing a case."
        , "case-seq 'v is is equivalent to adding @(seq v)@ in the source code." ] .+ Shallow
    , external "case-inline-alternative" (promoteExprR caseInlineAlternativeR :: RewriteH Core)
        [ "Inline the case wildcard binder as the case-alternative pattern everywhere in the case alternatives." ] .+ Deep
    , external "case-inline-scrutinee" (promoteExprR caseInlineScrutineeR :: RewriteH Core)
        [ "Inline the case wildcard binder as the case scrutinee everywhere in the case alternatives." ] .+ Deep
    , external "case-merge-alts" (promoteExprR caseMergeAltsR :: RewriteH Core)
        [ "Merge all case alternatives into a single default case."
        , "The RHS of each alternative must be the same."
        , "case s of {pat1 -> e ; pat2 -> e ; ... ; patn -> e} ==> case s of {_ -> e}" ]
    , external "case-merge-alts-with-wild" (promoteExprR caseMergeAltsWithWildR :: RewriteH Core)
        [ "A cleverer version of 'mergeCaseAlts' that first attempts to"
        , "abstract out any occurrences of the alternative pattern using the wildcard binder." ] .+ Deep
    , external "case-elim" (promoteExprR caseElimR :: RewriteH Core)
        [ "case s of w; C vs -> e ==> e if w and vs are not free in e" ]     .+ Shallow
    , external "case-elim-inline-scrutinee" (promoteExprR caseElimInlineScrutineeR :: RewriteH Core)
        [ "Eliminate a case, inlining any occurrences of the case binder as the scrutinee." ] .+ Deep
    , external "case-elim-merge-alts" (promoteExprR caseElimMergeAltsR :: RewriteH Core)
        [ "Eliminate a case, merging the case alternatives into a single default alternative",
          "and inlining the case binder as the scrutinee (if possible)." ] .+ Deep
    , external "case-fold-wild" (promoteExprR caseFoldWildR :: RewriteH Core)
        [ "In the case alternatives, fold any occurrences of the case alt patterns to the wildcard binder." ]
    ]

------------------------------------------------------------------------------

-- | case s of w; C vs -> e ==> e if w and vs are not free in e
caseElimR :: Rewrite c HermitM CoreExpr
caseElimR = prefixFailMsg "Case elimination failed: " $
            withPatFailMsg (wrongExprForm "Case s bnd ty alts") $
 do Case _ bnd _ alts <- idR
    case alts of
        [(_, vs, e)] -> do fvs <- applyInContextT exprFreeVarsT e
                           guardMsg (isEmptyVarSet $ intersectVarSet (mkVarSet (bnd:vs)) fvs) "wildcard or pattern binders free in RHS."
                           return e
        _ -> fail "more than one case alternative."

------------------------------------------------------------------------------

-- | (case s of alt1 -> e1; alt2 -> e2) v ==> case s of alt1 -> e1 v; alt2 -> e2 v
caseFloatAppR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatAppR = prefixFailMsg "Case floating from App function failed: " $
  do
    captures    <- appT (map mkVarSet <$> caseAltVarsT) exprFreeVarsT (flip (map . intersectVarSet))
    wildCapture <- appT caseWildIdT exprFreeVarsT elemVarSet
    appT ((if not wildCapture then idR else alphaCaseBinder Nothing)
          >>> caseAllR idR idR idR (\i -> if isEmptyVarSet (captures !! i) then idR else alphaAlt)
         )
          idR
          (\(Case s b _ty alts) v -> let newTy = exprType (App (case head alts of (_,_,f) -> f) v)
                                     in Case s b newTy $ mapAlts (flip App v) alts)

-- | @f (case s of alt1 -> e1; alt2 -> e2)@ ==> @case s of alt1 -> f e1; alt2 -> f e2@
--   Only safe if @f@ is strict.
caseFloatArgR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatArgR = prefixFailMsg "Case floating from App argument failed: " $
  do
    captures    <- appT exprFreeVarsT (map mkVarSet <$> caseAltVarsT) (map . intersectVarSet)
    wildCapture <- appT exprFreeVarsT caseWildIdT (flip elemVarSet)
    appT idR
         ((if not wildCapture then idR else alphaCaseBinder Nothing)
          >>> caseAllR idR idR idR (\i -> if isEmptyVarSet (captures !! i) then idR else alphaAlt)
         )
         (\f (Case s b _ty alts) -> let newTy = exprType (App f (case head alts of (_,_,e) -> e))
                                    in Case s b newTy $ mapAlts (App f) alts)

-- | case (case s1 of alt11 -> e11; alt12 -> e12) of alt21 -> e21; alt22 -> e22
--   ==>
--   case s1 of
--     alt11 -> case e11 of alt21 -> e21; alt22 -> e22
--     alt12 -> case e12 of alt21 -> e21; alt22 -> e22
caseFloatCaseR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatCaseR = prefixFailMsg "Case floating from Case failed: " $
  do
    captures <- caseT (map mkVarSet <$> caseAltVarsT) idR mempty (const altFreeVarsExclWildT) (\ vss bndr () fs -> map (intersectVarSet (unionVarSets $ map ($ bndr) fs)) vss)
    -- does the binder of the inner case, shadow a free variable in any of the outer case alts?
    -- notice, caseBinderVarT returns a singleton list
    wildCapture <- caseT caseWildIdT idR mempty (const altFreeVarsExclWildT) (\ innerBndr bndr () fvs -> innerBndr `elemVarSet` unionVarSets (map ($ bndr) fvs))
    caseT ((if not wildCapture then idR else alphaCaseBinder Nothing)
           >>> caseAllR idR idR idR (\i -> if isEmptyVarSet (captures !! i) then idR else alphaAlt)
          )
          idR
          idR
          (const idR)
          (\ (Case s1 b1 _ alts1) b2 ty alts2 -> Case s1 b1 ty $ mapAlts (\s -> Case s b2 ty alts2) alts1)

-- | let v = case s of alt1 -> e1 in e ==> case s of alt1 -> let v = e1 in e
caseFloatLetR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatLetR = prefixFailMsg "Case floating from Let failed: " $
  do vs <- letNonRecT idR caseAltVarsT mempty (\ letVar caseVars () -> letVar `elem` concat caseVars)
     let bdsAction = if not vs then idR else nonRecAllR idR alphaCase
     letT bdsAction idR $ \ (NonRec v (Case s b _ alts)) e -> Case s b (exprType e) $ mapAlts (flip Let e . NonRec v) alts

-- | cast (case s of p -> e) co ==> case s of p -> cast e co
caseFloatCastR :: MonadCatch m => Rewrite c m CoreExpr
caseFloatCastR = prefixFailMsg "Case float from cast failed: " $
                withPatFailMsg (wrongExprForm "Cast (Case s bnd ty alts) co") $
    do Cast (Case s bnd _ alts) co <- idR
       let alts' = mapAlts (flip Cast co) alts
       return $ Case s bnd (coreAltsType alts') alts'

-- | Float a Case whatever the context.
caseFloatR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatR = setFailMsg "Unsuitable expression for Case floating." $
    caseFloatAppR <+ caseFloatArgR <+ caseFloatCaseR <+ caseFloatLetR <+ caseFloatCastR

------------------------------------------------------------------------------

-- | Unfloat a Case whatever the context.
caseUnfloatR :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
caseUnfloatR = setFailMsg "Case unfloating failed." $
    caseUnfloatAppR <+ caseUnfloatArgsR

-- | Unimplemented!
caseUnfloatAppR :: Monad m => Rewrite c m CoreExpr
caseUnfloatAppR = fail "caseUnfloatApp: TODO"

caseUnfloatArgsR :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
caseUnfloatArgsR = prefixFailMsg "Case unfloating into arguments failed: " $
                   withPatFailMsg (wrongExprForm "Case s v t alts") $
    do Case s wild _ty alts <- idR
       (vss, fs, argss) <- caseT mempty mempty mempty (\ _ -> altT mempty (\ _ -> idR) callT $ \ () vs (fn, args) -> (vs, fn, args))
                                                      (\ () () () alts' -> unzip3 [ (wild:vs, fn, args) | (vs,fn,args) <- alts' ])
       guardMsg (equivalentBy exprAlphaEq fs) "alternatives are not parallel in function call."
       let fvs = [ varSetElems $ unionVarSets $ map exprFreeVars $ f:tyArgs
                 | (f,args) <- zip fs argss
                 , let tyArgs = takeWhile isTyCoArg args ] -- pattern binders can be existential types
       guardMsg (all null $ zipWith intersect fvs vss) "function bound by case binders."
       let argss' = transpose argss
       guardMsg (all (equivalentBy exprAlphaEq) $ filter (isTyCoArg . head) argss') "function applied at different types."
       return $ mkCoreApps (head fs) [ if isTyCoArg (head args)
                                       then head args
                                       else let alts' = [ (ac, vs, arg) | ((ac,vs,_),arg) <- zip alts args ]
                                            in Case s wild (coreAltsType alts') alts'
                                     | args <- argss' ]

------------------------------------------------------------------------------

caseReduceR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseReduceR = setFailMsg "Unsuitable expression for Case reduction." $
              caseReduceDataconR <+ caseReduceLiteralR

-- NB: LitAlt cases don't do evaluation
caseReduceLiteralR :: MonadCatch m => Rewrite c m CoreExpr
caseReduceLiteralR = prefixFailMsg "Case reduction failed: " $
                     withPatFailMsg (wrongExprForm "Case (Lit l) v t alts") $
    do Case s wild _ alts <- idR
#if __GLASGOW_HASKELL__ > 706
       let in_scope = mkInScopeSet (mkVarEnv [ (v,v) | v <- varSetElems (exprFreeVars s) ])
       case exprIsLiteral_maybe (in_scope, idUnfolding) s of
#else
       case exprIsLiteral_maybe idUnfolding s of
#endif
        Nothing -> fail "scrutinee is not a literal."
        Just l  -> do guardMsg (not (litIsLifted l)) "cannot case-reduce lifted literals" -- see Trac #5603
                      case findAlt (LitAlt l) alts of
                        Nothing          -> fail "no matching alternative."
                        Just (_, _, rhs) -> return $ mkCoreLet (NonRec wild (Lit l)) rhs

-- | Case-of-known-constructor rewrite.
caseReduceDataconR :: forall c. (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseReduceDataconR = prefixFailMsg "Case reduction failed: " $
                     withPatFailMsg (wrongExprForm "Case e v t alts")
                     go
  where
    go :: Rewrite c HermitM CoreExpr
    go = do Case e wild _ alts <- idR
#if __GLASGOW_HASKELL__ > 706
            let in_scope = mkInScopeSet (mkVarEnv [ (v,v) | v <- varSetElems (exprFreeVars e) ])
            case exprIsConApp_maybe (in_scope, idUnfolding) e of
#else
            case exprIsConApp_maybe idUnfolding e of
#endif
              Nothing                -> fail "head of scrutinee is not a data constructor."
              Just (dc, univTys, es) -> case findAlt (DataAlt dc) alts of
                Nothing             -> fail "no matching alternative."
                Just (dc', vs, rhs) -> -- dc' is either DEFAULT or dc
                                       -- NB: It is possible that es contains one or more existentially quantified types.
                                       let fvss    = map exprFreeVars $ map Type univTys ++ es
                                           shadows = [ v | (v,n) <- zip vs [1..], any (elemVarSet v) (drop n fvss) ]
                                       in if | any (elemVarSet wild) fvss -> alphaCaseBinder Nothing >>> go
                                             | not (null shadows)     -> caseOneR (fail "scrutinee") (fail "binder") (fail "type") (\ _ -> acceptR (\ (dc'',_,_) -> dc'' == dc') >>> alphaAltVars shadows) >>> go
                                             | null shadows           -> return $ flip mkCoreLets rhs $ zipWith NonRec (wild : vs) (e : es)
-- WARNING: The alpha-renaming to avoid variable capture has not been tested.  We need testing infrastructure!

-- | Case split a free identifier in an expression:
--
-- E.g. Assume expression e which mentions i :: [a]
--
-- e ==> case i of i
--         []     -> e
--         (a:as) -> e
caseSplitR :: TH.Name -> Rewrite c HermitM CoreExpr
caseSplitR nm = prefixFailMsg "caseSplit failed: " $
               do i <- matchingFreeIdT nm
                  let (tycon, tys) = splitTyConApp (idType i)
                      aNms         = map (:[]) $ cycle ['a'..'z']
                  contextfreeT $ \ e -> do dcsAndVars <- mapM (\ dc -> (dc,) <$> sequence [ newIdH a ty | (a,ty) <- zip aNms $ dataConInstArgTys dc tys ])
                                                              (tyConDataCons tycon)
                                           return $ Case (Var i) i (exprType e) [ (DataAlt dc, as, e) | (dc,as) <- dcsAndVars ]

-- | Force evaluation of an identifier by introducing a case.
--   This is equivalent to adding @(seq v)@ in the source code.
--
-- e -> case v of v
--        _ -> e
caseSeqR :: TH.Name -> Rewrite c HermitM CoreExpr
caseSeqR nm = prefixFailMsg "caseSeq failed: " $
             do i <- matchingFreeIdT nm
                arr $ \ e -> Case (Var i) i (exprType e) [(DEFAULT, [], e)]

-- auxillary function for use by caseSplit and caseSeq
matchingFreeIdT :: Monad m => TH.Name -> Translate c m CoreExpr Id
matchingFreeIdT nm = do
  fvs <- exprFreeIdsT
  case varSetElems (filterVarSet (cmpTHName2Var nm) fvs) of
    []    -> fail "provided name is not free."
    [i]   -> return i
    vs    -> fail ("provided name matches " ++ show (length vs) ++ " free identifiers.")

-- | Like caseSplit, but additionally inlines the constructor applications
-- for each occurance of the named variable.
--
-- > caseSplitInline nm = caseSplit nm >>> anybuR (inlineName nm)
caseSplitInlineR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => TH.Name -> Rewrite c HermitM Core
caseSplitInlineR nm = promoteR (caseSplitR nm) >>> anybuR (promoteExprR $ inlineNameR nm)

------------------------------------------------------------------------------

caseInlineBinderR :: forall c. (ExtendPath c Crumb, AddBindings c, ReadBindings c) => CaseBinderInlineOption -> Rewrite c HermitM CoreExpr
caseInlineBinderR opt =
  do w <- caseWildIdT
     caseAllR idR idR idR $ \ _ -> setFailMsg "no inlinable occurrences." $
                                   do depth <- varBindingDepthT w
                                      extractR $ anybuR (promoteExprR (configurableInlineR (CaseBinderOnly opt) (varIsOccurrenceOfT w depth)) :: Rewrite c HermitM Core)

-- | Inline the case wildcard binder as the case scrutinee everywhere in the case alternatives.
caseInlineScrutineeR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseInlineScrutineeR = prefixFailMsg "case-inline-scrutinee failed: " $
                       caseInlineBinderR Scrutinee

-- | Inline the case wildcard binder as the case-alternative pattern everywhere in the case alternatives.
caseInlineAlternativeR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
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
                    guardMsg (not $ null alts) "zero alternatives cannot be merged."
                    let rhss = [ rhs | (_,_,rhs) <- alts ]
                    guardMsg (equivalentBy exprAlphaEq rhss) "right-hand sides are not all equal."
                    guardMsg (all altVarsUnused alts) "variables bound in case alt pattern appear free in alt right-hand side."
                    return $ Case e w ty [(DEFAULT,[],head rhss)]

-- | In the case alternatives, fold any occurrences of the case alt patterns to the wildcard binder.
caseFoldWildR :: forall c.  (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFoldWildR = prefixFailMsg "case-fold-wild failed: " $
                do w <- caseWildIdT
                   caseAllR idR idR idR $ \ _ -> do depth <- varBindingDepthT w
                                                    extractR $ anybuR (promoteExprR (foldVarR w (Just depth)) :: Rewrite c HermitM Core)

-- | A cleverer version of 'mergeCaseAlts' that first attempts to abstract out any occurrences of the alternative pattern using the wildcard binder.
caseMergeAltsWithWildR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseMergeAltsWithWildR = prefixFailMsg "merge-case-alts-with-wild failed: " $
                         withPatFailMsg (wrongExprForm "Case e w ty alts") $
                         tryR caseFoldWildR >>> caseMergeAltsR

-- | Eliminate a case, inlining any occurrences of the case binder as the scrutinee.
caseElimInlineScrutineeR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseElimInlineScrutineeR = tryR caseInlineScrutineeR >>> caseElimR

-- | Eliminate a case, merging the case alternatives into a single default alternative and inlining the case binder as the scrutinee (if possible).
caseElimMergeAltsR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseElimMergeAltsR = tryR caseFoldWildR >>> tryR caseMergeAltsR >>> caseElimInlineScrutineeR

------------------------------------------------------------------------------

altVarsUnused :: CoreAlt -> Bool
altVarsUnused (_,vs,rhs) = all (`notElemVarSet` exprFreeVars rhs) vs

------------------------------------------------------------------------------
