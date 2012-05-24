-- Andre Santos' Local Transformations (Ch 3 in his dissertation)
module Language.HERMIT.Primitive.Local.Case where

import GhcPlugins

import Data.List (nub)
import Control.Applicative

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitMonad
import Language.HERMIT.External

import Language.HERMIT.Primitive.GHC

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------

externals :: [External]
externals =
         [ external "case-elimination" (promoteR $ not_defined "case-elimination")
                     [ "case v1 of v2 -> e ==> e[v1/v2]" ] .+ Experiment
         , external "case-merging" (promoteR $ not_defined "case-merging")
                     [ "case v of ...; d -> case v of alt -> e ==> case v of ...; alt -> e[v/d]" ] .+ Experiment
         , external "default-binding-elim" (promoteR $ not_defined "default-binding-elim")
                     [ "case v of ...;w -> e ==> case v of ...;w -> e[v/w]" ] .+ Experiment
         , external "let-float-case" (promoteR $ not_defined "let-float-case")
                     [ "case (let v = ev in e) of ... ==> let v = ev in case e of ..." ] .+ Experiment
         , external "case-float-app" (promoteR $ not_defined "case-float-app")
                     [ "(case ec of alt -> e) v ==> case ec of alt -> e v" ] .+ Experiment
         , external "case-float-case" (promoteR $ not_defined "case-float-case")
                     [ "case (case ec of alt1 -> e1) of alta -> ea ==> case ec of alt1 -> case e1 of alta -> ea" ] .+ Experiment
         , external "case-reduce" (promoteR caseReduce)
                     [ "case-of-known-constructor"
                     , "case C v1..vn of C w1..wn -> e ==> e[v1/w1..vn/wn]" ] .+ Bash .+ CaseCmd
         ]

not_defined :: String -> RewriteH CoreExpr
not_defined nm = rewrite $ \ c e -> fail $ nm ++ " not implemented!"

-- | Case-of-known-constructor rewrite
caseReduce :: RewriteH CoreExpr
caseReduce = liftMT $ \ e -> case e of
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

