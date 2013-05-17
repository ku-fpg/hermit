{-# LANGUAGE MultiWayIf #-}

module Language.HERMIT.Primitive.Local.Case
       ( -- * Rewrites on Case Expressions
         externals
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
       )
where


import GhcPlugins

import Data.List
import Data.Monoid
import Control.Arrow

import Language.HERMIT.Core
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.GHC
import Language.HERMIT.External

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.GHC hiding (externals)
import Language.HERMIT.Primitive.Inline hiding (externals)
import Language.HERMIT.Primitive.AlphaConversion hiding (externals)

import qualified Language.Haskell.TH as TH

-- NOTE: these are hard to test in small examples, as GHC does them for us, so use with caution
------------------------------------------------------------------------------

-- | Externals relating to Case expressions.
externals :: [External]
externals =
    [ -- I'm not sure this is possible. In core, v2 can only be a Constructor, Lit, or DEFAULT
      -- In the last case, v1 is already inlined in e. So we can't construct v2 as a Var.
      --   external "case-elimination" (promoteR $ not_defined "case-elimination" :: RewriteH Core)
      --     [ "case v1 of v2 -> e ==> e[v1/v2]" ]                                         .+ Unimplemented .+ Eval
      --   -- Again, don't think the lhs of this rule is possible to construct in core.
      -- , external "case-merging" (promoteR $ not_defined "case-merging" :: RewriteH Core)
      --     [ "case v of ...; d -> case v of alt -> e ==> case v of ...; alt -> e[v/d]" ] .+ Unimplemented .+ Eval
      external "case-float-app" (promoteExprR caseFloatApp :: RewriteH Core)
        [ "(case ec of alt -> e) v ==> case ec of alt -> e v" ]              .+ Commute .+ Shallow .+ Bash
    , external "case-float-arg" (promoteExprR caseFloatArg :: RewriteH Core)
        [ "f (case s of alt -> e) ==> case s of alt -> f e" ]                .+ Commute .+ Shallow .+ PreCondition
    , external "case-float-case" (promoteExprR caseFloatCase :: RewriteH Core)
        [ "case (case ec of alt1 -> e1) of alta -> ea ==> case ec of alt1 -> case e1 of alta -> ea" ] .+ Commute .+ Eval .+ Bash
    , external "case-float-cast" (promoteExprR caseFloatCast)
        [ "cast (case s of p -> e) co ==> case s of p -> cast e co" ]        .+ Shallow .+ Commute .+ Bash
    , external "case-float-let" (promoteExprR caseFloatLet :: RewriteH Core)
        [ "let v = case ec of alt1 -> e1 in e ==> case ec of alt1 -> let v = e1 in e" ] .+ Commute .+ Shallow .+ Bash
    , external "case-float" (promoteExprR caseFloat :: RewriteH Core)
        [ "Float a Case whatever the context." ]                             .+ Commute .+ Shallow .+ PreCondition
    , external "case-unfloat" (promoteExprR caseUnfloat :: RewriteH Core)
        [ "Unfloat a Case whatever the context." ]                             .+ Commute .+ Shallow .+ PreCondition
    , external "case-unfloat-args" (promoteExprR caseUnfloatArgs :: RewriteH Core)
        [ "Unfloat a Case whose alternatives are parallel applications of the same function." ] .+ Commute .+ Shallow .+ PreCondition
    , external "case-unfloat-app" (promoteExprR caseUnfloatApp :: RewriteH Core)
        [ "Unfloat a Case whole alternatives are applications of different functions with the same arguments." ] .+ Commute .+ Shallow .+ PreCondition
    , external "case-reduce" (promoteExprR caseReduce :: RewriteH Core)
        [ "case-reduce-datacon <+ case-reduce-literal" ]                     .+ Shallow .+ Eval .+ Bash
    , external "case-reduce-datacon" (promoteExprR caseReduceDatacon :: RewriteH Core)
        [ "case-of-known-constructor"
        , "case C v1..vn of C w1..wn -> e ==> let { w1 = v1 ; .. ; wn = vn } in e" ]    .+ Shallow .+ Eval
    , external "case-reduce-literal" (promoteExprR caseReduceLiteral :: RewriteH Core)
        [ "case L of L -> e ==> e" ]                                         .+ Shallow .+ Eval
    , external "case-split" (promoteExprR . caseSplit :: TH.Name -> RewriteH Core)
        [ "case-split 'x"
        , "e ==> case x of C1 vs -> e; C2 vs -> e, where x is free in e" ]
    , external "case-split-inline" (caseSplitInline :: TH.Name -> RewriteH Core)
        [ "Like case-split, but additionally inlines the matched constructor "
        , "applications for all occurances of the named variable." ]
    ]

------------------------------------------------------------------------------

-- | (case s of alt1 -> e1; alt2 -> e2) v ==> case s of alt1 -> e1 v; alt2 -> e2 v
caseFloatApp :: RewriteH CoreExpr
caseFloatApp = prefixFailMsg "Case floating from App function failed: " $
  do
    captures    <- appT caseAltVarsT freeVarsT (flip (map . intersect))
    wildCapture <- appT caseWildIdT freeVarsT elem
    appT ((if not wildCapture then idR else alphaCaseBinder Nothing)
          >>> caseAllR idR (\i -> if null (captures !! i) then idR else alphaAlt)
         )
          idR
          (\(Case s b _ty alts) v -> let newTy = exprType (App (case head alts of (_,_,f) -> f) v)
                                     in Case s b newTy $ mapAlts (flip App v) alts)

-- | @f (case s of alt1 -> e1; alt2 -> e2)@ ==> @case s of alt1 -> f e1; alt2 -> f e2@
--   Only safe if @f@ is strict.
caseFloatArg :: RewriteH CoreExpr
caseFloatArg = prefixFailMsg "Case floating from App argument failed: " $
  do
    captures    <- appT freeVarsT caseAltVarsT (map . intersect)
    wildCapture <- appT freeVarsT caseWildIdT (flip elem)
    appT idR
         ((if not wildCapture then idR else alphaCaseBinder Nothing)
          >>> caseAllR idR (\i -> if null (captures !! i) then idR else alphaAlt)
         )
         (\f (Case s b _ty alts) -> let newTy = exprType (App f (case head alts of (_,_,e) -> e))
                                    in Case s b newTy $ mapAlts (App f) alts)

-- | case (case s1 of alt11 -> e11; alt12 -> e12) of alt21 -> e21; alt22 -> e22
--   ==>
--   case s1 of
--     alt11 -> case e11 of alt21 -> e21; alt22 -> e22
--     alt12 -> case e12 of alt21 -> e21; alt22 -> e22
caseFloatCase :: RewriteH CoreExpr
caseFloatCase = prefixFailMsg "Case floating from Case failed: " $
  do
    captures <- caseT caseAltVarsT (const altFreeVarsExclWildT) (\ vss bndr _ fs -> map (intersect (concatMap ($ bndr) fs)) vss)
    -- does the binder of the inner case, shadow a free variable in any of the outer case alts?
    -- notice, caseBinderVarT returns a singleton list
    wildCapture <- caseT caseWildIdT (const altFreeVarsExclWildT) (\ innerBndr bndr _ fvs -> innerBndr `elem` concatMap ($ bndr) fvs)
    caseT ((if not wildCapture then idR else alphaCaseBinder Nothing)
           >>> caseAllR idR (\i -> if null (captures !! i) then idR else alphaAlt)
          )
          (const idR)
          (\ (Case s1 b1 _ alts1) b2 ty alts2 -> Case s1 b1 ty $ mapAlts (\s -> Case s b2 ty alts2) alts1)

-- | let v = case s of alt1 -> e1 in e ==> case s of alt1 -> let v = e1 in e
caseFloatLet :: RewriteH CoreExpr
caseFloatLet = prefixFailMsg "Case floating from Let failed: " $
  do vs <- letNonRecT caseAltVarsT idR (\ letVar caseVars _ -> elem letVar $ concat caseVars)
     let bdsAction = if not vs then idR else nonRecR alphaCase
     letT bdsAction idR $ \ (NonRec v (Case s b _ alts)) e -> Case s b (exprType e) $ mapAlts (flip Let e . NonRec v) alts

-- | cast (case s of p -> e) co ==> case s of p -> cast e co
caseFloatCast :: RewriteH CoreExpr
caseFloatCast = prefixFailMsg "Case float from cast failed: " $
                withPatFailMsg (wrongExprForm "Cast (Case s bnd ty alts) co") $
    do Cast (Case s bnd _ alts) co <- idR
       let alts' = mapAlts (flip Cast co) alts
       return $ Case s bnd (coreAltsType alts') alts'

-- | Float a Case whatever the context.
caseFloat :: RewriteH CoreExpr
caseFloat = setFailMsg "Unsuitable expression for Case floating." $
    caseFloatApp <+ caseFloatArg <+ caseFloatCase <+ caseFloatLet <+ caseFloatCast

------------------------------------------------------------------------------

caseUnfloat :: RewriteH CoreExpr
caseUnfloat = setFailMsg "Case unfloating failed." $
    caseUnfloatApp <+ caseUnfloatArgs

caseUnfloatApp :: RewriteH CoreExpr
caseUnfloatApp = fail "caseUnfloatApp: TODO"

caseUnfloatArgs :: RewriteH CoreExpr
caseUnfloatArgs = prefixFailMsg "Case unfloating into arguments failed: " $
                  withPatFailMsg (wrongExprForm "Case s v t alts") $
    do Case s wild _ty alts <- idR
       (vss, fs, argss) <- caseT mempty (\_ -> altT callT $ \ _ac vs (fn, args) -> (vs, fn, args))
                                        (\ () _ _ alts -> unzip3 [ (wild:vs, fn, args) | (vs,fn,args) <- alts ])
       guardMsg (exprsEqual fs) "alternatives are not parallel in function call."
       guardMsg (all null $ zipWith intersect (map coreExprFreeVars fs) vss) "function bound by case binders."
       return $ mkCoreApps (head fs) [ if isTyCoArg (head args)
                                       then head args -- TODO: is is possible for well-type case to have different
                                                      -- type arguments in different alternatives? Obviously not with
                                                      -- monomorphic types, but maybe with polymorphism?
                                       else let alts' = [ (ac, vs, arg) | ((ac,vs,_),arg) <- zip alts args ]
                                            in Case s wild (coreAltsType alts') alts'
                                     | args <- transpose argss ]

------------------------------------------------------------------------------

caseReduce :: RewriteH CoreExpr
caseReduce = setFailMsg "Unsuitable expression for Case reduction." $
             caseReduceDatacon <+ caseReduceLiteral

-- NB: LitAlt cases don't do evaluation
caseReduceLiteral :: RewriteH CoreExpr
caseReduceLiteral = prefixFailMsg "Case reduction failed: " $
                    withPatFailMsg (wrongExprForm "Case (Lit l) v t alts") $
    do Case s wild _ alts <- idR
       case exprIsLiteral_maybe idUnfolding s of
        Nothing -> fail "scrutinee is not a literal."
        Just l  -> do guardMsg (not (litIsLifted l)) "cannot case-reduce lifted literals" -- see Trac #5603
                      case findAlt (LitAlt l) alts of
                        Nothing          -> fail "no matching alternative."
                        Just (_, _, rhs) -> return $ mkCoreLet (NonRec wild (Lit l)) rhs

-- | Case-of-known-constructor rewrite.
caseReduceDatacon :: RewriteH CoreExpr
caseReduceDatacon = prefixFailMsg "Case reduction failed: " $
                    withPatFailMsg (wrongExprForm "Case e v t alts")
                    go
  where
    go :: RewriteH CoreExpr
    go = do Case e wild _ alts <- idR
            case exprIsConApp_maybe idUnfolding e of
              Nothing                -> fail "head of scrutinee is not a data constructor."
              Just (dc, univTys, es) -> case findAlt (DataAlt dc) alts of
                Nothing             -> fail "no matching alternative."
                Just (dc', vs, rhs) -> -- dc' is either DEFAULT or dc
                                       -- NB: It is possible that es contains one or more existentially quantified types.
                                       let fvss    = map coreExprFreeVars $ map Type univTys ++ es
                                           shadows = [ v | (v,n) <- zip vs [1..], any (elem v) (drop n fvss) ]
                                       in if | any (elem wild) fvss  -> alphaCaseBinder Nothing >>> go
                                             | not (null shadows)    -> caseOneR (fail "scrutinee") (\ _ -> acceptR (\ (dc'',_,_) -> dc'' == dc') >>> alphaAltVars shadows) >>> go
                                             | null shadows          -> return $ flip mkCoreLets rhs $ zipWith NonRec (wild : vs) (e : es)
-- WARNING: The alpha-renaming to avoid variable capture has not been tested.  We need testing infrastructure!

-- | Case split a free variable in an expression:
--
-- Assume expression e which mentions x :: [a]
--
-- e ==> case x of x
--         [] -> e
--         (a:b) -> e
caseSplit :: TH.Name -> RewriteH CoreExpr
caseSplit nm = do
    frees <- freeIdsT
    contextfreeT $ \ e ->
        case [ i | i <- frees, cmpTHName2Var nm i ] of
            []    -> fail "caseSplit: provided name is not free"
            (i:_) -> do
                let (tycon, tys) = splitTyConApp (idType i)
                    dcs = tyConDataCons tycon
                    aNms = map (:[]) $ cycle ['a'..'z']
                dcsAndVars <- mapM (\dc -> do
                                        as <- sequence [ newIdH a ty | (a,ty) <- zip aNms $ dataConInstArgTys dc tys ]
                                        return (dc,as)) dcs
                return $ Case (Var i) i (exprType e) [ (DataAlt dc, as, e) | (dc,as) <- dcsAndVars ]

-- | Like caseSplit, but additionally inlines the constructor applications
-- for each occurance of the named variable.
--
-- > caseSplitInline nm = caseSplit nm >>> anybuR (inlineName nm)
caseSplitInline :: TH.Name -> RewriteH Core
caseSplitInline nm = promoteR (caseSplit nm) >>> anybuR (promoteExprR $ inlineName nm)

------------------------------------------------------------------------------
