{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

module Language.HERMIT.Primitive.Case where

import GhcPlugins hiding ((<>))

import Language.HERMIT.Types
import Language.HERMIT.External
import Language.KURE

externals :: External
externals = external "caseReduce" (promoteR caseReduce) [ "case-of-known-constructor" ]

-- | Case-of-known-constructor rewrite
caseReduce :: RewriteH CoreExpr
caseReduce = rewrite $ \ _c e -> case e of
    (Case s _ _ alts) -> case isDataCon s of
                            Nothing -> fail "caseReduce failed, not a DataCon"
                            Just (sc, fs) -> case [ (bs, rhs) | (DataAlt dc, bs, rhs) <- alts, sc == dc ] of
                                                [(bs,e')] -> return $ nestedLets (zip bs fs) e'
                                                []   -> fail "caseReduce failed, no matching alternative (impossible?!)"
                                                _    -> fail "caseReduce failed, more than one matching alt (impossible?!)"
    _ -> fail "caseReduce failed, not a Case"

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
nestedLets :: [(b, Expr b)] -> Expr b -> Expr b
nestedLets [] e = e
nestedLets ((b,rhs):bs) e = Let (NonRec b rhs) $ nestedLets bs e
