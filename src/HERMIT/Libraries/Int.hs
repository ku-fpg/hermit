{-# LANGUAGE OverloadedStrings #-}
module HERMIT.Libraries.Int where

import Control.Arrow

import qualified Data.Map as M

import HERMIT.GHC hiding (intTy)
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Name
import HERMIT.Dictionary.Common
import HERMIT.Dictionary.GHC

{-
Defines the following lemmas:

forall n m.  (m == n) = (n == m)
forall n m.  (m < n ) = (n > m)
forall n m.  (m <= n) = (n >= m)
forall n m.  (m >= n) = (n < m)

forall n m.  (m <= n) = False  =>  (m == n) = False
forall n m.  (m == n) = True  =>  (m <= n) = True

forall n m.  (min n m)  =  (min m n)
forall n m.  (max n m)  =  (max m n)
forall n m.  (min n m <= n) = True
forall n m.  (max n m >= n) = True
-}

lemmas :: LemmaLibrary
lemmas = do
    intTy <- findTypeT "Prelude.Int"

    nId <- constT $ newIdH "n" intTy
    mId <- constT $ newIdH "m" intTy

    let n = varToCoreExpr nId
        m = varToCoreExpr mId
        appTo i e = return $ mkCoreApp (varToCoreExpr i) e
        appToInt i = appTo i (Type intTy)
        appToDict e = do
            let (aTys, _) = splitFunTys (exprType e)
            case aTys of
                (ty:_) | isDictTy ty -> return ty >>> buildDictionaryT >>> arr (mkCoreApp e)
                _ -> fail "first argument is not a dictionary."

        appMN e = mkCoreApps e [m,n]
        appNM e = mkCoreApps e [n,m]
        mkEL l r = mkL (Equiv l r)
        mkL cl = Lemma (Quantified [mId,nId] cl) BuiltIn NotUsed False
        mkIL al ar cl cr = mkL (Impl (Quantified [] $ Equiv al ar) (Quantified [] $ Equiv cl cr))

    eqE <- findIdT "Data.Eq.==" >>= appToInt >>= appToDict

    gtE <- findIdT "Data.Ord.>" >>= appToInt >>= appToDict
    ltE <- findIdT "Data.Ord.<" >>= appToInt >>= appToDict
    gteE <- findIdT "Data.Ord.>=" >>= appToInt >>= appToDict
    lteE <- findIdT "Data.Ord.<=" >>= appToInt >>= appToDict
    minE <- findIdT "Data.Ord.min" >>= appToInt >>= appToDict
    maxE <- findIdT "Data.Ord.max" >>= appToInt >>= appToDict

    trueE <- varToCoreExpr <$> findIdT "Data.Bool.True"
    falseE <- varToCoreExpr <$> findIdT "Data.Bool.False"

    return $ M.fromList
                [ ("EqCommutativeInt", mkEL (appMN eqE) (appNM eqE))
                , ("LtGtInt", mkEL (appMN ltE) (appNM gtE))
                , ("LteGteInt", mkEL (appMN lteE) (appNM gteE))
                , ("GteLtInt", mkEL (appMN gteE) (appNM ltE))
                , ("LteFalseImpliesEqFalseInt", mkIL (appMN lteE) falseE (appMN eqE) falseE)
                , ("EqTrueImpliesLteTrueInt", mkIL (appMN eqE) trueE (appMN lteE) trueE)
                , ("MinCommutativeInt", mkEL (appMN minE) (appNM minE))
                , ("MaxCommutativeInt", mkEL (appMN maxE) (appNM maxE))
                , ("MinLteInt", mkEL (mkCoreApps lteE [appNM minE, n]) trueE)
                , ("MaxGteInt", mkEL (mkCoreApps gteE [appNM maxE, n]) trueE)
                ]
