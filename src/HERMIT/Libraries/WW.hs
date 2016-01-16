{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module HERMIT.Libraries.WW (lemmas) where

import HERMIT.Lemma
import HERMIT.GHC hiding (($$), (<>))
import HERMIT.Kure
import HERMIT.Name

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Function
import HERMIT.Dictionary.GHC
import HERMIT.Dictionary.Reasoning

import Prelude hiding (abs)

lemmas :: LemmaLibrary
lemmas = workerWrapperLemmaT

-------------------------------------------------

-- | worker/wrapper
--
-- abs :: B -> A
-- rep :: A -> B
-- f :: A -> A
--
-- abs . rep = id   \/   abs . rep . f = f   \/   fix (abs . rep . f) = fix f
-----------------------------------------------------------------------------
--           fix f = abs (fix (rep . f . abs)) = abs (rep (fix f))
--                           ^ 1B ^                   ^ 2B ^
--
workerWrapperLemmaT :: LemmaLibrary
workerWrapperLemmaT = do
    idId <- findIdT "Data.Function.id"
    fixId <- findIdT "Data.Function.fix"
    contextonlyT $ \ c -> do
        -- aTv :: Var, aTy :: Type
        [aTv, bTv] <- mapM newTyVar ["a","b"]

        let [aTy, bTy] = map mkTyVarTy [aTv, bTv]

        abs <- newIdH "abs" (bTy --> aTy)
        rep <- newIdH "rep" (aTy --> bTy)
        f <- newIdH "f" (aTy --> aTy)

        -- abs . rep = id
        lhsA <- inContextM c $ buildCompositionT (toCE abs) (toCE rep)
#if __GLASGOW_HASKELL__ > 710
        let preA = lhsA === mkCoreApp (text "workerWrapperLemmaT") (toCE idId) (toCE aTv)
#else
        let preA = lhsA === mkCoreApp (toCE idId) (toCE aTv)
#endif

        -- abs . rep . f = f
        repAfterF <- inContextM c $ buildCompositionT (toCE rep) (toCE f)
        lhsB <- inContextM c $ buildCompositionT (toCE abs) repAfterF
        let preB = lhsB === f

        -- fix (abs . rep . f) = fix f
        lhsC <- fixId $$ lhsB
        fixf <- fixId $$ f
        let preC = lhsC === fixf

        -- 1B
        fAfterAbs <- inContextM c $ buildCompositionT (toCE f) (toCE abs)
        comp1B <- inContextM c $ buildCompositionT (toCE rep) fAfterAbs
        rhs1B <- (abs $$) =<< (fixId $$ comp1B)
        let oneB = fixf === rhs1B

        -- 2B
        rhs2B <- (abs $$) =<< (rep $$ fixf)
        let twoB = fixf === rhs2B

        return $ mconcat
            [ newLemma "ww-split-1B" $
                mkForall [aTv, bTv, abs, rep, f] $
                    ("ww-split-1B-antecedent", preA \/ preB \/ preC) ==> oneB
            , newLemma "ww-split-2B" $
                mkForall [aTv, bTv, abs, rep, f] $
                    ("ww-split-1B-antecedent", preA \/ preB \/ preC) ==> twoB
            ]

-------------------------------------------------

newTyVar :: MonadUnique m => String -> m TyVar
newTyVar nm = newTyVarH nm liftedTypeKind

-------------------------------------------------
