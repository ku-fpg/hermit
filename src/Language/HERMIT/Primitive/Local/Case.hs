{-# LANGUAGE CPP, MultiWayIf, ScopedTypeVariables, FlexibleContexts, TupleSections #-}

module Language.HERMIT.Primitive.Local.Case
    ( -- * Rewrites on Case Expressions
      externals
    , caseElim
    , caseFloatApp
    , caseFloatArg
    , caseFloatCase
    , caseFloatCast
    , caseFloatLet
    , caseFloat
    , caseUnfloat
    , caseUnfloatApp
    , caseUnfloatArgs
    , caseReduce
    , caseReduceDatacon
    , caseReduceLiteral
    , caseSplit
    , caseSplitInline
    , caseMergeAltsR
    , caseMergeAltsWithWildR
    , caseMergeAltsElimR
    ) where

import GhcPlugins

import Data.List
import Data.Monoid
import Data.Set (intersection, fromList, toList, member, notMember, unions)
import qualified Data.Set as S
import Control.Arrow
import Control.Applicative

import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.GHC
import Language.HERMIT.External

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.GHC hiding (externals)
import Language.HERMIT.Primitive.Inline hiding (externals)
import Language.HERMIT.Primitive.AlphaConversion hiding (externals)
import Language.HERMIT.Primitive.Fold (foldVarR)

import qualified Language.Haskell.TH as TH

-- NOTE: these are hard to test in small examples, as GHC does them for us, so use with caution
------------------------------------------------------------------------------

-- | Externals relating to Case expressions.
externals :: [External]
externals =
    [ external "case-elim" (promoteExprR caseElim :: RewriteH Core)
        [ "case s of w; C vs -> e ==> e if w and vs are not free in e" ]     .+ Shallow
    , external "case-float-app" (promoteExprR caseFloatApp :: RewriteH Core)
        [ "(case ec of alt -> e) v ==> case ec of alt -> e v" ]              .+ Commute .+ Shallow .+ Bash
    , external "case-float-arg" (promoteExprR caseFloatArg :: RewriteH Core)
        [ "f (case s of alt -> e) ==> case s of alt -> f e" ]                .+ Commute .+ Shallow .+ PreCondition
    , external "case-float-case" (promoteExprR caseFloatCase :: RewriteH Core)
        [ "case (case ec of alt1 -> e1) of alta -> ea ==> case ec of alt1 -> case e1 of alta -> ea" ] .+ Commute .+ Eval .+ Bash
    , external "case-float-cast" (promoteExprR caseFloatCast :: RewriteH Core)
        [ "cast (case s of p -> e) co ==> case s of p -> cast e co" ]        .+ Shallow .+ Commute .+ Bash
    , external "case-float-let" (promoteExprR caseFloatLet :: RewriteH Core)
        [ "let v = case ec of alt1 -> e1 in e ==> case ec of alt1 -> let v = e1 in e" ] .+ Commute .+ Shallow .+ Bash
    , external "case-float" (promoteExprR caseFloat :: RewriteH Core)
        [ "Float a Case whatever the context." ]                             .+ Commute .+ Shallow .+ PreCondition
    , external "case-unfloat" (promoteExprR caseUnfloat :: RewriteH Core)
        [ "Unfloat a Case whatever the context." ]                             .+ Commute .+ Shallow .+ PreCondition
    , external "case-unfloat-args" (promoteExprR caseUnfloatArgs :: RewriteH Core)
        [ "Unfloat a Case whose alternatives are parallel applications of the same function." ] .+ Commute .+ Shallow .+ PreCondition
    -- , external "case-unfloat-app" (promoteExprR caseUnfloatApp :: RewriteH Core)
    --     [ "Unfloat a Case whole alternatives are applications of different functions with the same arguments." ] .+ Commute .+ Shallow .+ PreCondition
    , external "case-reduce" (promoteExprR caseReduce :: RewriteH Core)
        [ "case-reduce-datacon <+ case-reduce-literal" ]                     .+ Shallow .+ Eval .+ Bash
    , external "case-reduce-datacon" (promoteExprR caseReduceDatacon :: RewriteH Core)
        [ "case-of-known-constructor"
        , "case C v1..vn of C w1..wn -> e ==> let { w1 = v1 ; .. ; wn = vn } in e" ]    .+ Shallow .+ Eval
    , external "case-reduce-literal" (promoteExprR caseReduceLiteral :: RewriteH Core)
        [ "case L of L -> e ==> e" ]                                         .+ Shallow .+ Eval
    , external "case-split" (promoteExprR . caseSplit :: TH.Name -> RewriteH Core)
        [ "case-split 'x"
        , "e ==> case x of C1 vs -> e; C2 vs -> e, where x is free in e" ] .+ Shallow
    , external "case-split-inline" (caseSplitInline :: TH.Name -> RewriteH Core)
        [ "Like case-split, but additionally inlines the matched constructor "
        , "applications for all occurances of the named variable." ] .+ Deep
    , external "case-seq" (promoteExprR . caseSeq :: TH.Name -> RewriteH Core)
        [ "Force evaluation of a variable by introducing a case."
        , "case-seq 'v is is equivalent to adding @(seq v)@ in the source code." ] .+ Shallow
    , external "case-merge-alts" (promoteExprR caseMergeAltsR :: RewriteH Core)
        [ "Merge all case alternatives into a single default case."
        , "The RHS of each alternative must be the same."
        , "case s of {pat1 -> e ; pat2 -> e ; ... ; patn -> e} ==> case s of {_ -> e}" ]
    , external "case-merge-alts-with-wild" (promoteExprR caseMergeAltsWithWildR :: RewriteH Core)
        [ "A cleverer version of 'mergeCaseAlts' that first attempts to"
        , "abstract out any occurrences of the alternative pattern using the wildcard binder." ] .+ Deep
    , external "case-merge-alts-elim" (promoteExprR caseMergeAltsElimR :: RewriteH Core)
        [ "Merge the case alternatives into a single default alternative (if possible),"
        , "and then eliminate the case." ] .+ Deep
    , external "case-fold-wild" (promoteExprR caseFoldWildR :: RewriteH Core)
        [ "In the case alternatives, fold any occurrences of the case alt patterns to the wildcard binder." ]
    ]

------------------------------------------------------------------------------

-- | case s of w; C vs -> e ==> e if w and vs are not free in e
caseElim :: Rewrite c HermitM CoreExpr
caseElim = prefixFailMsg "Case elimination failed: " $
           withPatFailMsg (wrongExprForm "Case s bnd ty alts") $ do
    Case _ bnd _ alts <- idR
    case alts of
        [(_, vs, e)] -> do fvs <- applyInContextT freeVarsT e
                           guardMsg (S.null $ intersection (fromList (bnd:vs)) fvs) "wildcard or pattern binders free in RHS."
                           return e
        _ -> fail "more than one case alternative."

-- | (case s of alt1 -> e1; alt2 -> e2) v ==> case s of alt1 -> e1 v; alt2 -> e2 v
caseFloatApp :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatApp = prefixFailMsg "Case floating from App function failed: " $
  do
    captures    <- appT (map fromList <$> caseAltVarsT) freeVarsT (flip (map . intersection))
    wildCapture <- appT caseWildIdT freeVarsT member
    appT ((if not wildCapture then idR else alphaCaseBinder Nothing)
          >>> caseAllR idR idR idR (\i -> if S.null (captures !! i) then idR else alphaAlt)
         )
          idR
          (\(Case s b _ty alts) v -> let newTy = exprType (App (case head alts of (_,_,f) -> f) v)
                                     in Case s b newTy $ mapAlts (flip App v) alts)

-- | @f (case s of alt1 -> e1; alt2 -> e2)@ ==> @case s of alt1 -> f e1; alt2 -> f e2@
--   Only safe if @f@ is strict.
caseFloatArg :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatArg = prefixFailMsg "Case floating from App argument failed: " $
  do
    captures    <- appT freeVarsT (map fromList <$> caseAltVarsT) (map . intersection)
    wildCapture <- appT freeVarsT caseWildIdT (flip member)
    appT idR
         ((if not wildCapture then idR else alphaCaseBinder Nothing)
          >>> caseAllR idR idR idR (\i -> if S.null (captures !! i) then idR else alphaAlt)
         )
         (\f (Case s b _ty alts) -> let newTy = exprType (App f (case head alts of (_,_,e) -> e))
                                    in Case s b newTy $ mapAlts (App f) alts)

-- | case (case s1 of alt11 -> e11; alt12 -> e12) of alt21 -> e21; alt22 -> e22
--   ==>
--   case s1 of
--     alt11 -> case e11 of alt21 -> e21; alt22 -> e22
--     alt12 -> case e12 of alt21 -> e21; alt22 -> e22
caseFloatCase :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatCase = prefixFailMsg "Case floating from Case failed: " $
  do
    captures <- caseT (map fromList <$> caseAltVarsT) idR mempty (const altFreeVarsExclWildT) (\ vss bndr () fs -> map (intersection (unions $ map ($ bndr) fs)) vss)
    -- does the binder of the inner case, shadow a free variable in any of the outer case alts?
    -- notice, caseBinderVarT returns a singleton list
    wildCapture <- caseT caseWildIdT idR mempty (const altFreeVarsExclWildT) (\ innerBndr bndr () fvs -> innerBndr `member` unions (map ($ bndr) fvs))
    caseT ((if not wildCapture then idR else alphaCaseBinder Nothing)
           >>> caseAllR idR idR idR (\i -> if S.null (captures !! i) then idR else alphaAlt)
          )
          idR
          idR
          (const idR)
          (\ (Case s1 b1 _ alts1) b2 ty alts2 -> Case s1 b1 ty $ mapAlts (\s -> Case s b2 ty alts2) alts1)

-- | let v = case s of alt1 -> e1 in e ==> case s of alt1 -> let v = e1 in e
caseFloatLet :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloatLet = prefixFailMsg "Case floating from Let failed: " $
  do vs <- letNonRecT idR caseAltVarsT mempty (\ letVar caseVars () -> letVar `elem` concat caseVars)
     let bdsAction = if not vs then idR else nonRecAllR idR alphaCase
     letT bdsAction idR $ \ (NonRec v (Case s b _ alts)) e -> Case s b (exprType e) $ mapAlts (flip Let e . NonRec v) alts

-- | cast (case s of p -> e) co ==> case s of p -> cast e co
caseFloatCast :: MonadCatch m => Rewrite c m CoreExpr
caseFloatCast = prefixFailMsg "Case float from cast failed: " $
                withPatFailMsg (wrongExprForm "Cast (Case s bnd ty alts) co") $
    do Cast (Case s bnd _ alts) co <- idR
       let alts' = mapAlts (flip Cast co) alts
       return $ Case s bnd (coreAltsType alts') alts'

-- | Float a Case whatever the context.
caseFloat :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFloat = setFailMsg "Unsuitable expression for Case floating." $
    caseFloatApp <+ caseFloatArg <+ caseFloatCase <+ caseFloatLet <+ caseFloatCast

------------------------------------------------------------------------------

-- | Unfloat a Case whatever the context.
caseUnfloat :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
caseUnfloat = setFailMsg "Case unfloating failed." $
    caseUnfloatApp <+ caseUnfloatArgs

-- | Unimplemented!
caseUnfloatApp :: Monad m => Rewrite c m CoreExpr
caseUnfloatApp = fail "caseUnfloatApp: TODO"

caseUnfloatArgs :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m CoreExpr
caseUnfloatArgs = prefixFailMsg "Case unfloating into arguments failed: " $
                  withPatFailMsg (wrongExprForm "Case s v t alts") $
    do Case s wild _ty alts <- idR
       (vss, fs, argss) <- caseT mempty mempty mempty (\ _ -> altT mempty (\ _ -> idR) callT $ \ () vs (fn, args) -> (vs, fn, args))
                                                      (\ () () () alts' -> unzip3 [ (wild:vs, fn, args) | (vs,fn,args) <- alts' ])
       guardMsg (exprsEqual fs) "alternatives are not parallel in function call."
       guardMsg (all null $ zipWith intersect (map (toList.coreExprFreeVars) fs) vss) "function bound by case binders."
       let argss' = transpose argss
       guardMsg (all exprsEqual $ filter (isTyCoArg . head) argss') "function applied at different types."
       return $ mkCoreApps (head fs) [ if isTyCoArg (head args)
                                       then head args -- TODO: deal with existentials by tupling
                                       else let alts' = [ (ac, vs, arg) | ((ac,vs,_),arg) <- zip alts args ]
                                            in Case s wild (coreAltsType alts') alts'
                                     | args <- argss' ]

------------------------------------------------------------------------------

caseReduce :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseReduce = setFailMsg "Unsuitable expression for Case reduction." $
             caseReduceDatacon <+ caseReduceLiteral

-- NB: LitAlt cases don't do evaluation
caseReduceLiteral :: MonadCatch m => Rewrite c m CoreExpr
caseReduceLiteral = prefixFailMsg "Case reduction failed: " $
                    withPatFailMsg (wrongExprForm "Case (Lit l) v t alts") $
    do Case s wild _ alts <- idR
#if __GLASGOW_HASKELL__ > 706
       let in_scope = mkInScopeSet (mkVarEnv [ (v,v) | v <- S.toList (coreExprFreeVars s) ])
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
caseReduceDatacon :: forall c. (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseReduceDatacon = prefixFailMsg "Case reduction failed: " $
                    withPatFailMsg (wrongExprForm "Case e v t alts")
                    go
  where
    go :: Rewrite c HermitM CoreExpr
    go = do Case e wild _ alts <- idR
#if __GLASGOW_HASKELL__ > 706
            let in_scope = mkInScopeSet (mkVarEnv [ (v,v) | v <- S.toList (coreExprFreeVars e) ])
            case exprIsConApp_maybe (in_scope, idUnfolding) e of
#else
            case exprIsConApp_maybe idUnfolding e of
#endif
              Nothing                -> fail "head of scrutinee is not a data constructor."
              Just (dc, univTys, es) -> case findAlt (DataAlt dc) alts of
                Nothing             -> fail "no matching alternative."
                Just (dc', vs, rhs) -> -- dc' is either DEFAULT or dc
                                       -- NB: It is possible that es contains one or more existentially quantified types.
                                       let fvss    = map coreExprFreeVars $ map Type univTys ++ es
                                           shadows = [ v | (v,n) <- zip vs [1..], any (member v) (drop n fvss) ]
                                       in if | any (member wild) fvss -> alphaCaseBinder Nothing >>> go
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
caseSplit :: TH.Name -> Rewrite c HermitM CoreExpr
caseSplit nm = prefixFailMsg "caseSplit failed: " $
               do i <- matchingFreeId nm
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
caseSeq :: TH.Name -> Rewrite c HermitM CoreExpr
caseSeq nm = prefixFailMsg "caseSeq failed: " $
             do i <- matchingFreeId nm
                arr $ \ e -> Case (Var i) i (exprType e) [(DEFAULT, [], e)]

-- auxillary function for use by caseSplit and caseSeq
matchingFreeId :: Monad m => TH.Name -> Translate c m CoreExpr Id
matchingFreeId nm = do
  fvs <- freeIdsT
  case filter (cmpTHName2Var nm) (toList fvs) of
    []    -> fail "provided name is not free."
    [i]   -> return i
    vs    -> fail ("provided name matches " ++ show (length vs) ++ " free identifiers.")

-- | Like caseSplit, but additionally inlines the constructor applications
-- for each occurance of the named variable.
--
-- > caseSplitInline nm = caseSplit nm >>> anybuR (inlineName nm)
caseSplitInline :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => TH.Name -> Rewrite c HermitM Core
caseSplitInline nm = promoteR (caseSplit nm) >>> anybuR (promoteExprR $ inlineName nm)

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
                    guardMsg (exprsEqual rhss) "right-hand sides are not all equal."
                    guardMsg (all altVarsUnused alts) "variables bound in case alt pattern appear free in alt right-hand side."
                    return $ Case e w ty [(DEFAULT,[],head rhss)]

altVarsUnused :: CoreAlt -> Bool
altVarsUnused (_,vs,rhs) = all (`notMember` coreExprFreeVars rhs) vs

-- | In the case alternatives, fold any occurrences of the case alt patterns to the wildcard binder.
caseFoldWildR :: forall c.  (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseFoldWildR = prefixFailMsg "case-fold-wild failed: " $
                do w <- caseWildIdT
                   caseAllR idR idR idR $ \ _ -> do depth <- hermitDepth <$> contextT -- The most recent depth is that of the wildcard binding at this point.
                                                                                      -- This feels a bit fragile.
                                                                                      -- An alternative is to alpha-rename the wildcard before we start.
                                                    extractR $ anybuR (promoteExprR (foldVarR w (Just depth)) :: Rewrite c HermitM Core)

-- | A cleverer version of 'mergeCaseAlts' that first attempts to abstract out any occurrences of the alternative pattern using the wildcard binder.
caseMergeAltsWithWildR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseMergeAltsWithWildR = prefixFailMsg "merge-case-alts-with-wild failed: " $
                         withPatFailMsg (wrongExprForm "Case e w ty alts") $
                         tryR caseFoldWildR >>> caseMergeAltsR

-- | Merge the case alternatives into a single default alternative (if possible), and then eliminate the case.
caseMergeAltsElimR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseMergeAltsElimR = tryR caseFoldWildR >>> tryR caseMergeAltsR >>> tryR caseInlineScrutineeR >>> caseElim

------------------------------------------------------------------------------
