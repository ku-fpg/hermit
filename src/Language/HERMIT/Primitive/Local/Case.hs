module Language.HERMIT.Primitive.Local.Case
       ( -- * Rewrites on Case Expressions
         caseExternals
       , letFloatCase
       , caseFloatApp
       , caseFloatArg
       , caseFloatCase
       , caseFloatLet
       , caseFloat
       , caseReduce
       , caseSplit
       , caseSplitInline
       )
where


import GhcPlugins

import Data.List
import Control.Arrow
import Control.Applicative

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
           external "let-float-case" (promoteExprR letFloatCase :: RewriteH Core)
                     [ "case (let v = ev in e) of ... ==> let v = ev in case e of ..." ]  .+ Commute .+ Shallow .+ Eval .+ Bash
         , external "case-float-app" (promoteExprR caseFloatApp :: RewriteH Core)
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
                     [ "case-of-known-constructor"
                     , "case C v1..vn of C w1..wn -> e ==> e[v1/w1..vn/wn]" ] .+ Shallow .+ Eval .+ Bash
         , external "case-split" (promoteExprR . caseSplit :: TH.Name -> RewriteH Core)
                [ "case-split 'x"
                , "e ==> case x of C1 vs -> e; C2 vs -> e, where x is free in e" ]
         , external "case-split-inline" (caseSplitInline :: TH.Name -> RewriteH Core)
                [ "Like case-split, but additionally inlines the matched constructor "
                , "applications for all occurances of the named variable." ]
         ]

-- | case (let v = e1 in e2) of alts ==> let v = e1 in case e2 of alts
letFloatCase :: RewriteH CoreExpr
letFloatCase = prefixFailMsg "Let floating from Case failed: " $
  do
     captures <- caseT letVarsT (const (pure ())) $ \ vs _ _ _ -> vs
     cFrees   <- freeVarsT -- so we get type variables too
     caseT (if null (cFrees `intersect` captures) then idR else alphaLet)
           (const idR)
           (\ (Let bnds e) b ty alts -> Let bnds (Case e b ty alts))

-- | (case s of alt1 -> e1; alt2 -> e2) v ==> case s of alt1 -> e1 v; alt2 -> e2 v
caseFloatApp :: RewriteH CoreExpr
caseFloatApp = prefixFailMsg "Case floating from App function failed: " $
  do
    captures      <- appT caseAltVarsT freeVarsT (flip (map . intersect))
    binderCapture <- appT caseBinderVarT freeVarsT intersect
    appT ((if null binderCapture then idR else alphaCaseBinder Nothing)
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
    captures      <- appT freeVarsT caseAltVarsT (map . intersect)
    binderCapture <- appT freeVarsT caseBinderVarT intersect
    appT idR
         ((if null binderCapture then idR else alphaCaseBinder Nothing)
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
    captures <- caseT caseAltVarsT (const altFreeVarsT) $ \ vss bndr _ fs -> map (intersect (concatMap ($ bndr) fs)) vss
    -- does the binder of the inner case, shadow a free variable in any of the outer case alts?
    -- notice, caseBinderVarT returns a singleton list
    binderCapture <- caseT caseBinderVarT (const altFreeVarsT) $ \ innerBindr bndr _ fs -> intersect (concatMap ($ bndr) fs) innerBindr
    caseT ((if null binderCapture then idR else alphaCaseBinder Nothing)
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

-- | Case-of-known-constructor rewrite.
caseReduce :: RewriteH CoreExpr
caseReduce = letTransform >>> tryR (repeatR letSubstR)
    where letTransform = prefixFailMsg "Case reduction failed: " $
                         withPatFailMsg (wrongExprForm "Case e v t alts") $
                         do Case s binder _ alts <- idR
                            case isDataCon s of
                              Nothing -> fail "head of scrutinee is not a data constructor."
                              Just (dc, args) ->
                                case [ (bs, rhs) | (DataAlt dc', bs, rhs) <- alts, dc == dc' ] of
                                    [(bs,e')] -> let (tyArgs, valArgs) = span isTypeArg args
                                                     tyBndrs = takeWhile isTyVar bs -- it is possible the pattern constructor binds a type
                                                                                    -- if the constructor is existentially quantified
                                                     existentials = reverse $ take (length tyBndrs) $ reverse tyArgs
                                                  in return $ nestedLets e' $ (binder, s) : zip bs (existentials ++ valArgs)
                                    []   -> fail "no matching alternative."
                                    _    -> fail "more than one matching alternative."

-- | If expression is a constructor application, return the relevant bits.
isDataCon :: CoreExpr -> Maybe (DataCon, [CoreExpr])
isDataCon expr = case fn of
                    Var i -> do dc <- isDataConId_maybe i
                                return (dc, args)
                    _ -> fail "not a var"
    where (fn, args) = collectArgs expr

-- | We don't want to use the recursive let here, so nest a bunch of non-recursive lets
nestedLets :: CoreExpr -> [(Id, CoreExpr)] -> CoreExpr
nestedLets = foldr (\(b,rhs) -> Let $ NonRec b rhs)

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
        case [ i | i <- frees, cmpTHName2Id nm i ] of
            []    -> fail "caseSplit: provided name is not free"
            (i:_) -> do
                let (tycon, tys) = splitTyConApp (idType i)
                    dcs = tyConDataCons tycon
                    aNms = map (:[]) $ cycle ['a'..'z']
                dcsAndVars <- mapM (\dc -> do
                                        as <- sequence [ newVarH a ty | (a,ty) <- zip aNms $ dataConInstArgTys dc tys ]
                                        return (dc,as)) dcs
                return $ Case (Var i) i (exprType e) [ (DataAlt dc, as, e) | (dc,as) <- dcsAndVars ]

-- | Like caseSplit, but additionally inlines the constructor applications
-- for each occurance of the named variable.
--
-- > caseSplitInline nm = caseSplit nm >>> anybuR (inlineName nm)
caseSplitInline :: TH.Name -> RewriteH Core
caseSplitInline nm = promoteR (caseSplit nm) >>> anybuR (promoteExprR $ inlineName nm)

