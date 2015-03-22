{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, MultiWayIf #-}

module HERMIT.Dictionary.Induction
  ( -- * Induction
    externals
  , inductionOnR
  , inductionCaseSplit
  )
where

import Control.Arrow
import Control.Monad

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Monad
import HERMIT.Name

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Local.Case hiding (externals)
import HERMIT.Dictionary.Undefined hiding (externals)

------------------------------------------------------------------------------

externals :: [External]
externals =
    [ external "induction" (promoteQuantifiedR . inductionOnR . cmpHN2Var :: HermitName -> RewriteH LCore)
        [ "Induct on specified value quantifier." ]
    ]

------------------------------------------------------------------------------

inductionOnR :: (Id -> Bool) -> RewriteH Quantified
inductionOnR idPred = do
    let p b = idPred b && isId b
    Quantified bs cl <- idR
    guardMsg (any p bs) "specified identifier is not universally quantified in this lemma. (Induction cannot be performed on type quantifiers.)"
    let (as,b:bs') = break p bs -- safe because above guard
    guardMsg (not (any p bs')) "multiple matching quantifiers."

    ue <- mkUndefinedValT (varType b) -- undefined case
    cases <- liftM (ue:) $ constT $ caseExprsForM $ varToCoreExpr b

    let newBs = as ++ bs'
        substructural = filter (typeAlphaEq (varType b) . varType)

        go [] = return []
        go (e:es) = do
            -- we really should implement substClause
            let Quantified _ cl' = substQuantified b e $ Quantified [] cl
                fvs = varSetElems $ delVarSetList (localFreeVarsExpr e) newBs

            -- Generate induction hypotheses for the recursive cases.
            antes <- forM (substructural fvs) $ \ b' ->
                        withVarsInScope fvs $ transform $ \ c q ->
                            liftM discardUniVars $ instQuantified (boundVars c) (==b) (Var b') q

            rs <- go es
            return $ Quantified fvs (foldr (\q -> Impl q . Quantified []) cl' antes) : rs

    qs <- go cases

    let Quantified _ newClause = foldr1 (\q1 q2 -> Quantified [] (Conj q1 q2)) qs

    return $ Quantified newBs newClause

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


