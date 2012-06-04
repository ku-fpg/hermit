-- Andre Santos' Local Transformations (Ch 3 in his dissertation)
module Language.HERMIT.Primitive.Local.Case where

import GhcPlugins

import Data.List
import Control.Applicative
import Control.Arrow

import Language.HERMIT.HermitKure
import Language.HERMIT.External

import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Subst hiding (letSubstR)

-- NOTE: these are hard to test in small examples, as GHC does them for us, so use with caution
------------------------------------------------------------------------------

externals :: [External]
externals = map (.+ CaseCmd) $
         [ -- I'm not sure this is possible. In core, v2 can only be a Constructor, Lit, or DEFAULT
           -- In the last case, v1 is already inlined in e. So we can't construct v2 as a Var.
           external "case-elimination" (promoteR $ not_defined "case-elimination" :: RewriteH Core)
                     [ "case v1 of v2 -> e ==> e[v1/v2]" ]                                         .+ Unimplemented .+ Eval
           -- Again, don't think the lhs of this rule is possible to construct in core.
         , external "default-binding-elim" (promoteR $ not_defined "default-binding-elim" :: RewriteH Core)
                     [ "case v of ...;w -> e ==> case v of ...;w -> e[v/w]" ]                      .+ Unimplemented .+ Eval
           -- Again, don't think the lhs of this rule is possible to construct in core.
         , external "case-merging" (promoteR $ not_defined "case-merging" :: RewriteH Core)
                     [ "case v of ...; d -> case v of alt -> e ==> case v of ...; alt -> e[v/d]" ] .+ Unimplemented .+ Eval
         , external "let-float-case" (promoteR letFloatCase :: RewriteH Core)
                     [ "case (let v = ev in e) of ... ==> let v = ev in case e of ..." ]                           .+ Eval
         , external "case-float-app" (promoteR caseFloatApp :: RewriteH Core)
                     [ "(case ec of alt -> e) v ==> case ec of alt -> e v" ]                                       .+ Eval
         , external "case-float-arg" (promoteR caseFloatArg :: RewriteH Core)
                     [ "f (case s of alt -> e) ==> case s of alt -> f e" ] -- for paper                                        .+ Eval
         , external "case-float-case" (promoteR caseFloatCase :: RewriteH Core)
                     [ "case (case ec of alt1 -> e1) of alta -> ea ==> case ec of alt1 -> case e1 of alta -> ea" ] .+ Eval
         , external "case-reduce" (promoteR caseReduce :: RewriteH Core)
                     [ "case-of-known-constructor"
                     , "case C v1..vn of C w1..wn -> e ==> e[v1/w1..vn/wn]" ]                                      .+ Eval
         ]

not_defined :: String -> RewriteH CoreExpr
not_defined nm = rewrite $ \ c e -> fail $ nm ++ " not implemented!"

altVarsT :: TranslateH CoreAlt [Id]
altVarsT = altT (pure ()) (const const)

caseAltVarsT :: TranslateH CoreExpr [[Id]]
caseAltVarsT = caseT (pure ()) (const altVarsT) $ \ _ i _ ids -> map (i:) ids

letFloatCase :: RewriteH CoreExpr
letFloatCase = do Case (Let rec e) b ty alts <- idR
                  return $ Let rec (Case e b ty alts)

caseFloatApp :: RewriteH CoreExpr
caseFloatApp = do
    captures <- appT caseAltVarsT freeVarsT (flip (map . intersect))
    appT (caseAllR idR
                   (\i -> (if null (captures !! (i-1)) then idR else alphaAlt)))
         idR
         (\(Case s b _ty alts) v -> let newTy = exprType (App (case head alts of (_,_,f) -> f) v)
                                    in Case s b newTy [ (c, ids, App f v)
                                                      | (c,ids,f) <- alts ])

caseFloatArg :: RewriteH CoreExpr
caseFloatArg = do
    captures <- appT freeVarsT caseAltVarsT (map . intersect)
    appT idR
         (caseAllR idR
                   (\i -> (if null (captures !! (i-1)) then idR else alphaAlt)))
         (\f (Case s b _ty alts) -> let newTy = exprType (App f (case head alts of (_,_,e) -> e))
                                    in Case s b newTy [ (c, ids, App f e)
                                                      | (c,ids,e) <- alts ])

caseFloatCase :: RewriteH CoreExpr
caseFloatCase = do Case (Case s1 b1 ty1 alts1) b2 ty2 alts2 <- idR
                   return $ Case s1 b1 ty1 [ (c1, ids1, Case e1 b2 ty2 alts2) | (c1, ids1, e1) <- alts1 ]

-- | Case-of-known-constructor rewrite
caseReduce :: RewriteH CoreExpr
caseReduce = letTransform >>> repeatR letSubstR
    where letTransform = contextfreeT $ \ e -> case e of
            (Case s _ _ alts) -> case isDataCon s of
                                    Nothing -> fail "caseReduce failed, not a DataCon"
                                    Just (sc, fs) -> case [ (bs, rhs) | (DataAlt dc, bs, rhs) <- alts, sc == dc ] of
                                                        [(bs,e')] -> return $ nestedLets e' $ zip bs fs
                                                        []   -> fail "caseReduce failed, no matching alternative (impossible?!)"
                                                        _    -> fail "caseReduce failed, more than one matching alt (impossible?!)"
            _ -> fail "caseReduce failed, not a Case"

-- TODO: finish writing isDataCon to handle all Expr constructors properly
-- | Walk down the left spine of an App tree, looking for a DataCon
--   and keeping track of the fields as we go.
isDataCon :: CoreExpr -> Maybe (DataCon, [CoreExpr])
isDataCon expr = go expr []
    where go (App e a) fs = go e (a:fs)
          go (Var i)   fs | isId i = case idDetails i of
                                        DataConWorkId dc -> return (dc,fs)
                                        DataConWrapId dc -> return (dc,fs)
                                        _ -> Nothing
          go _ _ = Nothing -- probably not true, due to ticks and whathaveyou

-- | We don't want to use the recursive let here, so nest a bunch of non-recursive lets
nestedLets :: Expr b -> [(b, Expr b)] -> Expr b
nestedLets e = foldr (\(b,rhs) -> Let $ NonRec b rhs) e

