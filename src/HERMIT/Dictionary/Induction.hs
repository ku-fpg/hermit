{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}

module HERMIT.Dictionary.Induction
  ( -- * Induction
    externals
  , caseSplitOnR
  )
where

import Control.Monad
import Data.String

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Name

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Local.Case hiding (externals)
import HERMIT.Dictionary.Undefined hiding (externals)

------------------------------------------------------------------------------

externals :: [External]
externals =
    [ external "induction" (promoteQuantifiedR . caseSplitOnR True . cmpHN2Var :: HermitName -> RewriteH LCore)
        [ "Induct on specified value quantifier." ]
    , external "prove-by-cases" (promoteQuantifiedR . caseSplitOnR False . cmpHN2Var :: HermitName -> RewriteH LCore)
        [ "Case split on specified value quantifier." ]
    ]

------------------------------------------------------------------------------

caseSplitOnR :: Bool -> (Id -> Bool) -> RewriteH Quantified
caseSplitOnR induction idPred = do
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
            antes <- if induction
                     then forM (zip [(0::Int)..] $ substructural fvs) $ \ (i,b') ->
                            withVarsInScope fvs $ transform $ \ c q ->
                                let nm = fromString $ "ind-hyp-" ++ show i
                                in liftM ((nm,) . discardUniVars) $ instQuantified (boundVars c) (==b) (Var b') q
                     else return []

            rs <- go es
            return $ Quantified fvs (foldr (\(nm,q) -> Impl nm q . Quantified []) cl' antes) : rs

    qs <- go cases

    let Quantified _ newClause = foldr1 (\q1 q2 -> Quantified [] (Conj q1 q2)) qs

    return $ Quantified newBs newClause

