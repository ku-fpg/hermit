{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, MultiWayIf #-}

module HERMIT.Dictionary.Induction
  ( -- * Induction
    inductionCaseSplit
  )
where

import Control.Arrow

import HERMIT.Context
import HERMIT.Core
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Local.Case (caseSplitInlineR)
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
       Case _ _ _ alts <- withVarsInScope vs (caseSplitInlineR (varToCoreExpr i)) <<< return contrivedExpr
       let dataConCases = map compressAlts alts

       lhsUndefined <- extractR (replaceIdWithUndefinedR i) <<< return lhsE
       rhsUndefined <- extractR (replaceIdWithUndefinedR i) <<< return rhsE

       let undefinedCase = (Nothing,[],lhsUndefined,rhsUndefined)

       return (undefinedCase : dataConCases)

  where
    compressAlts :: CoreAlt -> (Maybe DataCon,[Var],CoreExpr,CoreExpr)
    compressAlts (DataAlt con,bs,Let (NonRec _ lhsE') (Let (NonRec _ rhsE') _)) = (Just con,bs,lhsE',rhsE')
    compressAlts _ = error "Bug in inductionCaseSplit"


