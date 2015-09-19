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

import Control.Arrow
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
    [ external "induction" (promoteClauseR . caseSplitOnR True . cmpHN2Var :: HermitName -> RewriteH LCore)
        [ "Induct on specified value quantifier." ]
    , external "prove-by-cases" (promoteClauseR . caseSplitOnR False . cmpHN2Var :: HermitName -> RewriteH LCore)
        [ "Case split on specified value quantifier." ]
    ]

------------------------------------------------------------------------------

-- TODO: revisit design here to make one level
caseSplitOnR :: Bool -> (Id -> Bool) -> RewriteH Clause
caseSplitOnR induction idPred = withPatFailMsg "induction can only be performed on universally quantified terms." $ do
    let p b = idPred b && isId b
    (bs, cl) <- arr collectQs
    guardMsg (any p bs) "specified identifier is not universally quantified in this lemma. (Induction cannot be performed on type quantifiers.)"
    let (as,b:bs') = break p bs -- safe because above guard
    guardMsg (not (any p bs')) "multiple matching quantifiers."

    ue <- mkUndefinedValT (varType b) -- undefined case
    cases <- liftM (ue:) $ constT $ caseExprsForM $ varToCoreExpr b

    let newBs = as ++ bs'
        substructural = filter (typeAlphaEq (varType b) . varType)

        go [] = return []
        go (e:es) = do
            let cl' = substClause b e cl
                fvs = varSetElems $ delVarSetList (localFreeVarsExpr e) newBs

            -- Generate induction hypotheses for the recursive cases.
            antes <- if induction
                     then forM (zip [(0::Int)..] $ substructural fvs) $ \ (i,b') ->
                            withVarsInScope fvs $ transform $ \ c q ->
                                let nm = fromString $ "ind-hyp-" ++ show i
                                in liftM ((nm,) . discardUniVars) $ instClause (boundVars c) (==b) (Var b') q
                     else return []

            rs <- go es
            return $ mkForall fvs (foldr (uncurry Impl) cl' antes) : rs

    qs <- go cases

    return $ mkForall newBs $ foldr1 Conj qs
