module Language.HERMIT.Primitive.Local.Case
       ( -- * Rewrites on Case Expressions
         caseExternals
       , caseFloatApp
       , caseFloatArg
       , caseFloatCase
       , caseFloatLet
       , caseFloat
       , caseReduce
       , caseReduceDatacon
       , caseReduceLiteral
       , caseSplit
       , caseSplitInline
       )
where


import GhcPlugins

import Data.List
import Control.Arrow

import Language.HERMIT.Core
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.GHC
import Language.HERMIT.External

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Inline
import Language.HERMIT.Primitive.AlphaConversion

import qualified Language.Haskell.TH as TH

-- NOTE: these are hard to test in small examples, as GHC does them for us, so use with caution
------------------------------------------------------------------------------

-- | Externals relating to Case expressions.
caseExternals :: [External]
caseExternals =
         [ -- I'm not sure this is possible. In core, v2 can only be a Constructor, Lit, or DEFAULT
           -- In the last case, v1 is already inlined in e. So we can't construct v2 as a Var.
         --   external "case-elimination" (promoteR $ not_defined "case-elimination" :: RewriteH Core)
         --             [ "case v1 of v2 -> e ==> e[v1/v2]" ]                                         .+ Unimplemented .+ Eval
         --   -- Again, don't think the lhs of this rule is possible to construct in core.
         -- , external "default-binding-elim" (promoteR $ not_defined "default-binding-elim" :: RewriteH Core)
         --             [ "case v of ...;w -> e ==> case v of ...;w -> e[v/w]" ]                      .+ Unimplemented .+ Eval
         --   -- Again, don't think the lhs of this rule is possible to construct in core.
         -- , external "case-merging" (promoteR $ not_defined "case-merging" :: RewriteH Core)
         --             [ "case v of ...; d -> case v of alt -> e ==> case v of ...; alt -> e[v/d]" ] .+ Unimplemented .+ Eval
           external "case-float-app" (promoteExprR caseFloatApp :: RewriteH Core)
                     [ "(case ec of alt -> e) v ==> case ec of alt -> e v" ]              .+ Commute .+ Shallow .+ Bash
         , external "case-float-arg" (promoteExprR caseFloatArg :: RewriteH Core)
                     [ "f (case s of alt -> e) ==> case s of alt -> f e" ]                .+ Commute .+ Shallow .+ PreCondition
         , external "case-float-case" (promoteExprR caseFloatCase :: RewriteH Core)
                     [ "case (case ec of alt1 -> e1) of alta -> ea ==> case ec of alt1 -> case e1 of alta -> ea" ] .+ Commute .+ Eval .+ Bash
         , external "case-float-let" (promoteExprR caseFloatLet :: RewriteH Core)
                     [ "let v = case ec of alt1 -> e1 in e ==> case ec of alt1 -> let v = e1 in e" ] .+ Commute .+ Shallow .+ Bash
         , external "case-float" (promoteExprR caseFloat :: RewriteH Core)
                     [ "Float a Case whatever the context." ] .+ Commute .+ Shallow .+ PreCondition
         , external "case-reduce" (promoteExprR caseReduce :: RewriteH Core)
                     [ "case-reduce-datacon <+ case-reduce-literal" ] .+ Shallow .+ Eval .+ Bash
         , external "case-reduce-datacon" (promoteExprR caseReduceDatacon :: RewriteH Core)
                     [ "case-of-known-constructor"
                     , "case C v1..vn of C w1..wn -> e ==> let { w1 = v1 ; .. ; wn = vn } in e" ] .+ Shallow .+ Eval
         , external "case-reduce-literal" (promoteExprR caseReduceLiteral :: RewriteH Core)
                     [ "case L of L -> e ==> e" ] .+ Shallow .+ Eval
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
                                     in Case s b newTy [ (c, ids, App f v)
                                                       | (c,ids,f) <- alts ])

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
                                    in Case s b newTy [ (c, ids, App f e)
                                                      | (c,ids,e) <- alts ])

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
          (\ (Case s1 b1 _ alts1) b2 ty alts2 -> Case s1 b1 ty [ (c1, ids1, Case e1 b2 ty alts2) | (c1, ids1, e1) <- alts1 ])

-- | let v = case ec of alt1 -> e1 in e ==> case ec of alt1 -> let v = e1 in e
caseFloatLet :: RewriteH CoreExpr
caseFloatLet = prefixFailMsg "Case floating from Let failed: " $
  do vs <- letNonRecT caseAltVarsT idR (\ letVar caseVars _ -> elem letVar $ concat caseVars)
     let bdsAction = if not vs then idR else nonRecR alphaCase
     letT bdsAction idR $ \ (NonRec v (Case s b ty alts)) e -> Case s b ty [ (con, ids, Let (NonRec v ec) e) | (con, ids, ec) <- alts]


-- | Float a Case whatever the context.
caseFloat :: RewriteH CoreExpr
caseFloat = setFailMsg "Unsuitable expression for Case floating." $
            caseFloatApp <+ caseFloatArg <+ caseFloatCase <+ caseFloatLet

caseReduce :: RewriteH CoreExpr
caseReduce = setFailMsg "Unsuitable expression for Case reduction." $
             caseReduceDatacon <+ caseReduceLiteral

-- NB: LitAlt cases don't do evaluation
caseReduceLiteral :: RewriteH CoreExpr
caseReduceLiteral =
             prefixFailMsg "Case reduction failed: " $
             withPatFailMsg (wrongExprForm "Case (Lit l) v t alts") $
             do Case (Lit l) wild _ alts <- idR
                guardMsg (not (litIsLifted l)) "cannot case-reduce lifted literals" -- see Trac #5603
                case findAlt (LitAlt l) alts of
                  Nothing          -> fail "no matching alternative."
                  Just (_, _, rhs) -> return $ mkCoreLet (NonRec wild (Lit l)) rhs

-- | Case-of-known-constructor rewrite.
caseReduceDatacon :: RewriteH CoreExpr
caseReduceDatacon =
             prefixFailMsg "Case reduction failed: " $
             withPatFailMsg (wrongExprForm "Case e v t alts") $
             do Case s wild _ alts <- idR
                case isDataCon s of
                  Nothing         -> fail "head of scrutinee is not a data constructor."
                  Just (dc, args) -> case findAlt (DataAlt dc) alts of
                                       Nothing           -> fail "no matching alternative."
                                       Just (_, bs, rhs) -> -- It is possible the pattern constructor binds a type if the constructor is existentially quantified.
                                                            -- trimConArgs drops the universally quantified types, but not the existentially quantified types.
                                                            let existentialsAndValArgs = trimConArgs (DataAlt dc) args
                                                             in return $ flip mkCoreLets rhs $ zipWith NonRec (wild : bs) (s : existentialsAndValArgs)  -- TODO: currently this can capture free variables with the nested lets, needs fixing.

-- | If expression is a constructor application, return the relevant bits.
isDataCon :: CoreExpr -> Maybe (DataCon, [CoreExpr])
isDataCon expr = case fn of
                    Var i -> do dc <- isDataConWorkId_maybe i
                                return (dc, args)
                    _ -> fail "not a var"
    where (fn, args) = collectArgs expr

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
