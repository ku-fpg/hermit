{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, MultiWayIf #-}

module HERMIT.Dictionary.Induction
  ( -- * Induction
    inductionCaseSplit
--  , inductionOnT
--  , listInductionOnT
  )
where

import Control.Arrow

-- import Data.List (delete)

import HERMIT.Context
import HERMIT.Core
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name
-- import HERMIT.Utilities (soleElement)

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Local.Case (caseSplitInlineR)
-- import HERMIT.Dictionary.Reasoning
import HERMIT.Dictionary.Undefined

------------------------------------------------------------------------------

-- TODO: Warning, this is very experimental

------------------------------------------------------------------------------

inductionCaseSplit :: (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb)
                   => [Var] -> Id -> CoreExpr -> CoreExpr -> Transform c HermitM x [(Maybe DataCon,[Var],CoreExpr,CoreExpr)]
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
       let dataConCases = map compressAlts alts

       lhsUndefined <- extractR (replaceIdWithUndefinedR i) <<< return lhsE
       rhsUndefined <- extractR (replaceIdWithUndefinedR i) <<< return rhsE

       let undefinedCase = (Nothing,[],lhsUndefined,rhsUndefined)

       return (undefinedCase : dataConCases)

  where
    compressAlts :: CoreAlt -> (Maybe DataCon,[Var],CoreExpr,CoreExpr)
    compressAlts (DataAlt con,bs,Let (NonRec _ lhsE') (Let (NonRec _ rhsE') _)) = (Just con,bs,lhsE',rhsE')
    compressAlts _ = error "Bug in inductionCaseSplit"


-- NOTE: Most of the Induction infrastructure has moved to HERMIT/Shell/Proof.hs


-- -- | A general induction principle.  TODO: Is this valid for infinite data types?  Probably not.
-- inductionOnT :: forall c. (AddBindings c, ReadBindings c, ReadPath c Crumb, ExtendPath c Crumb, Walker c Core)
--                     => (Id -> Bool) -> (DataCon -> [BiRewrite c HermitM CoreExpr] -> CoreExprEqualityProof c HermitM) -> Transform c HermitM CoreExprEquality ()
-- inductionOnT idPred genCaseAltProofs = prefixFailMsg "Induction failed: " $
--     do eq@(CoreExprEquality bs lhs rhs) <- idR

--        i <- setFailMsg "specified identifier is not universally quantified in this equality lemma." $ soleElement (filter idPred bs)

--        cases <- inductionCaseSplit bs i lhs rhs

--        -- TODO: will this work if vs contains TyVars or CoVars?  Maybe we need to sort the Vars in order: TyVars; CoVars; Ids.
--        let verifyInductiveCaseT :: (DataCon,[Var],CoreExpr,CoreExpr) -> Transform c HermitM x ()
--            verifyInductiveCaseT (con,vs,lhsE,rhsE) =
--                 let vs_matching_i_type = filter (typeAlphaEq (varType i) . varType) vs
--                     eqs = [ discardUniVars (instantiateCoreExprEq [(i,Var i')] eq) | i' <- vs_matching_i_type ]
--                     brs = map birewrite eqs -- These eqs now have no universally quantified variables.
--                                             -- Thus they can only be used on variables in the induction hypothesis.
--                                             -- TODO: consider whether this is unneccassarily restrictive
--                     caseEq = CoreExprEquality (delete i bs ++ vs) lhsE rhsE
--                 in return caseEq >>> verifyCoreExprEqualityT (genCaseAltProofs con brs)

--        mapM_ verifyInductiveCaseT cases

-- -- | An induction principle for lists.
-- listInductionOnT :: (AddBindings c, ReadBindings c, ReadPath c Crumb, ExtendPath c Crumb, Walker c Core)
--                 => (Id -> Bool) -- Id to case split on
--                 -> CoreExprEqualityProof c HermitM -- proof for [] case
--                 -> (BiRewrite c HermitM CoreExpr -> CoreExprEqualityProof c HermitM) -- proof for (:) case, given smaller proof
--                 -> Transform c HermitM CoreExprEquality ()
-- listInductionOnT idPred nilCaseProof consCaseProof = inductionOnT idPred $ \ con brs ->
--                                                                 if | con == nilDataCon   -> case brs of
--                                                                                                   [] -> nilCaseProof
--                                                                                                   _  -> error "Bug!"
--                                                                    | con == consDataCon  -> case brs of
--                                                                                                   [br] -> consCaseProof br
--                                                                                                   _    -> error "Bug!"
--                                                                    | otherwise           -> let msg = "Mystery constructor, this is a bug."
--                                                                                              in (fail msg, fail msg)

------------------------------------------------------------------------------
