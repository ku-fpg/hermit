{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, MultiWayIf #-}

module HERMIT.Dictionary.Induction
  ( -- * Induction
    inductionOnT
  , listInductionOnT
  )
where

import Control.Arrow

import Data.List (delete)

import HERMIT.Context
import HERMIT.Core
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Utilities (soleElement)

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Local.Case (caseSplitInlineR)
import HERMIT.Dictionary.Reasoning

------------------------------------------------------------------------------

-- TODO: Warning, this is very experimental

------------------------------------------------------------------------------

inductionCaseSplit :: forall c x. (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c) => [Var] -> Id -> CoreExpr -> CoreExpr -> Translate c HermitM x [(DataCon,[Var],CoreExpr,CoreExpr)]
inductionCaseSplit vs i lhsE rhsE =
    do -- first construct an expression containing both the LHS and the RHS
       il <- constT $ newIdH "dummyL" (exprKindOrType lhsE)
       ir <- constT $ newIdH "dummyR" (exprKindOrType rhsE)
       let contrivedExpr = Let (NonRec il lhsE)
                               (Let (NonRec ir rhsE)
                                    (Var i)
                               )

       -- then case split on the identifier, inlining the pattern
       -- we consider the other universally quantified variables to be in scope while doing so
       Case _ _ _ alts <- withVarsInScope vs (caseSplitInlineR (==i)) <<< return contrivedExpr

       constT (mapM compressAlts alts)

  where
    compressAlts :: CoreAlt -> HermitM (DataCon,[Var],CoreExpr,CoreExpr)
    compressAlts (DataAlt con,bs,Let (NonRec _ lhsE') (Let (NonRec _ rhsE') _)) = return (con,bs,lhsE',rhsE')
    compressAlts _ = fail "Bug in inductionCaseSplit"


-- | A general induction principle.  TODO: Is this valid for infinite data types?  Probably not.
inductionOnT :: forall c. (AddBindings c, ReadBindings c, ReadPath c Crumb, ExtendPath c Crumb, Walker c Core)
                    => (Id -> Bool) -> (DataCon -> [BiRewrite c HermitM CoreExpr] -> CoreExprEqualityProof c HermitM) -> Translate c HermitM CoreExprEquality ()
inductionOnT idPred genCaseAltProofs = prefixFailMsg "Induction failed: " $
    do eq@(CoreExprEquality bs lhs rhs) <- idR

       i <- setFailMsg "specified identifier is not universally quantified in this equality lemma." $ soleElement (filter idPred bs)

       cases <- inductionCaseSplit bs i lhs rhs

       -- TODO: will this work if vs contains TyVars or CoVars?  Maybe we need to sort the Vars in order: TyVars; CoVars; Ids.
       let verifyInductiveCaseT :: (DataCon,[Var],CoreExpr,CoreExpr) -> Translate c HermitM x ()
           verifyInductiveCaseT (con,vs,lhsE,rhsE) = let vs_matching_i_type = filter (typeAlphaEq (varType i) . varType) vs
                                                         eqs = [ discardUniVars (instantiateCoreExprEq [(i,Var i')] eq) | i' <- vs_matching_i_type ]
                                                         brs = map birewrite eqs -- These eqs now have no universally quantified variables.
                                                                                 -- Thus they can only be used on variables in the induction hypothesis.
                                                                                 -- TODO: consider whether this is unneccassarily restrictive
                                                         caseEq = CoreExprEquality (delete i bs ++ vs) lhsE rhsE
                                                      in return caseEq >>> verifyCoreExprEqualityT (genCaseAltProofs con brs)

       mapM_ verifyInductiveCaseT cases

  where
    discardUniVars :: CoreExprEquality -> CoreExprEquality
    discardUniVars (CoreExprEquality _ lhs rhs) = CoreExprEquality [] lhs rhs


-- | An induction principle for lists.
listInductionOnT :: (AddBindings c, ReadBindings c, ReadPath c Crumb, ExtendPath c Crumb, Walker c Core)
                => (Id -> Bool) -- Id to case split on
                -> CoreExprEqualityProof c HermitM -- proof for [] case
                -> (BiRewrite c HermitM CoreExpr -> CoreExprEqualityProof c HermitM) -- proof for (:) case, given smaller proof
                -> Translate c HermitM CoreExprEquality ()
listInductionOnT idPred nilCaseProof consCaseProof = inductionOnT idPred $ \ con brs ->
                                                                if | con == nilDataCon   -> case brs of
                                                                                                  [] -> nilCaseProof
                                                                                                  _  -> error "Bug!"
                                                                   | con == consDataCon  -> case brs of
                                                                                                  [br] -> consCaseProof br
                                                                                                  _    -> error "Bug!"
                                                                   | otherwise           -> let msg = "Mystery constructor, this is a bug."
                                                                                             in (fail msg, fail msg)

------------------------------------------------------------------------------
