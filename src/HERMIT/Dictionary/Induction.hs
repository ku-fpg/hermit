{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, MultiWayIf #-}

module HERMIT.Dictionary.Induction
  ( -- * Induction
    inductionOnT
  , listInductionOnT
  )
where

import Control.Arrow
import Control.Monad (zipWithM)

import Data.List (delete)

import HERMIT.Context
import HERMIT.Core
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad

import HERMIT.Dictionary.Common (findIdT)
import HERMIT.Dictionary.Local.Case (caseSplitInlineR)
import HERMIT.Dictionary.Reasoning
import HERMIT.Dictionary.Rules

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------

-- TODO: Warning, this is very experimental

------------------------------------------------------------------------------

inductionCaseSplit :: Id -> CoreExpr -> CoreExpr -> Translate c HermitM x [(DataCon,[Var],CoreExpr,CoreExpr)]
inductionCaseSplit i e1 e2 =
    do Case _ _ _ alts1 <- caseSplitInlineR i <<< return e1
       Case _ _ _ alts2 <- caseSplitInlineR i <<< return e2
       constT (zipWithM combineAlts alts1 alts2)
  where
    combineAlts :: CoreAlt -> CoreAlt -> HermitM (DataCon,[Var],CoreExpr,CoreExpr)
    combineAlts (DataAlt con1,vs1,e1) (DataAlt con2,vs2,e2) | con1 == con2 && vs1 == vs2 = return (con1,vs1,e1,e2)
    combineAlts _ _ = fail "Bug in inductionCaseSplit"

-- | A general induction principle for any inductive (i.e. finite) data type.
inductionOnT :: forall c. (AddBindings c, ReadBindings c, ReadPath c Crumb, ExtendPath c Crumb, Walker c Core)
                    => Id -> (DataCon -> [BiRewrite c HermitM CoreExpr] -> CoreExprEqualityProof c HermitM) -> Translate c HermitM CoreExprEquality ()
inductionOnT i genCaseAltProofs =
    do eq@(CoreExprEquality bs lhs rhs) <- idR
       guardMsg (i `elem` bs) ("identifier " ++ var2String i ++ " is not universally quantified in this equality lemma.")

       let bs_minus_i :: [CoreBndr]
           bs_minus_i = delete i bs

           -- bs_exprs :: [(Var,CoreExpr)]
           -- bs_exprs = [ (b,varToCoreExpr b) | b <- bs_minus_i ]

       cases <- inductionCaseSplit i lhs rhs

       -- TODO: will this work if vs contains TyVars or CoVars?  Maybe we need to sort the Vars in order: TyVars; CoVars; Ids.
       let verifyInductiveCaseT :: (DataCon,[Var],CoreExpr,CoreExpr) -> Translate c HermitM x ()
           verifyInductiveCaseT (con,vs,lhsE,rhsE) = let vs_matching_i_type = filter (typeAlphaEq (varType i) . varType) vs
                                                         eqs = [ discardUniVars (instantiateCoreExprEq [(i,Var i')] eq) | i' <- vs_matching_i_type ]
                                                         brs = map birewrite eqs -- These eqs now have no universally quantified variables.
                                                                                 -- Thus they can only be used on variables in the induction hypothesis.
                                                                                 -- TODO: consider whether this is unneccassarily restrictive
                                                         caseEq = CoreExprEquality (bs_minus_i ++ vs) lhsE rhsE
                                                      in return caseEq >>> verifyCoreExprEqualityT (genCaseAltProofs con brs)

       mapM_ verifyInductiveCaseT cases

  where
    discardUniVars :: CoreExprEquality -> CoreExprEquality
    discardUniVars (CoreExprEquality _ lhs rhs) = CoreExprEquality [] lhs rhs


-- | An induction principle for finite lists.
listInductionOnT :: (AddBindings c, ReadBindings c, ReadPath c Crumb, ExtendPath c Crumb, Walker c Core)
                => Id -- Id to case split on
                -> CoreExprEqualityProof c HermitM -- proof for [] case
                -> (BiRewrite c HermitM CoreExpr -> CoreExprEqualityProof c HermitM) -- proof for (:) case, given smaller proof
                -> Translate c HermitM CoreExprEquality ()
listInductionOnT i nilCaseRs consCaseRs = inductionOnT i $ \ con brs ->
                                                                if | con == nilDataCon   -> case brs of
                                                                                                  [] -> nilCaseRs
                                                                                                  _  -> error "Bug!"
                                                                   | con == consDataCon  -> case brs of
                                                                                                  [r] -> consCaseRs r
                                                                                                  _   -> error "Bug!"
                                                                   | otherwise           -> let msg = "Mystery constructor, this is a bug."
                                                                                             in (fail msg, fail msg)



-- verifyRuleByListInductionT :: (AddBindings c, ReadBindings c, ReadPath c Crumb, ExtendPath c Crumb, Walker c Core, BoundVars c, HasGlobalRdrEnv c, HasCoreRules c)
--             => RuleNameString -> TH.Name -> CoreExprEqualityProof c HermitM -> (BiRewrite c HermitM CoreExpr -> CoreExprEqualityProof c HermitM) -> Translate c HermitM a ()
-- verifyRuleByListInductionT ru_name id_name nilCaseRs consCaseRs =
--     do i <- findIdT id_name
--        ruleNameToEqualityT ru_name >>> listInductionOnT i nilCaseRs consCaseRs

------------------------------------------------------------------------------
