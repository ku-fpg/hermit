{-# LANGUAGE FlexibleContexts, RankNTypes #-}
module HERMIT.Dictionary.Function
    ( externals
    , staticArgR
    , staticArgPosR
    , staticArgPredR
    , staticArgTypesR
    )
where

import Control.Arrow

import Data.List (nub, intercalate, intersect, partition, transpose)

import HERMIT.Context
import HERMIT.Core
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC

import HERMIT.Dictionary.Common

externals ::  [External]
externals =
    [ external "static-arg" (promoteDefR staticArgR :: RewriteH Core)
        [ "perform the static argument transformation on a recursive function." ]
    , external "static-arg-types" (promoteDefR staticArgTypesR :: RewriteH Core)
        [ "perform the static argument transformation on a recursive function, only transforming type arguments." ]
    , external "static-arg-pos" (promoteDefR . staticArgPosR :: [Int] -> RewriteH Core)
        [ "perform the static argument transformation on a recursive function, only transforming the arguments specified (by index)." ]
    ]

------------------------------------------------------------------------------------------------------

-- | Traditional Static Argument Transformation
staticArgR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c) => Rewrite c HermitM CoreDef
staticArgR = staticArgPredR (return . map fst)

-- | Static Argument Transformation that only considers type arguments to be static.
staticArgTypesR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c) => Rewrite c HermitM CoreDef
staticArgTypesR = staticArgPredR (return . map fst . filter (isTyVar . snd))

-- | Static Argument Transformations which requires that arguments in the given position are static.
staticArgPosR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c) => [Int] -> Rewrite c HermitM CoreDef
staticArgPosR is' = staticArgPredR $ \ss' -> let is = nub is'
                                                 ss = map fst ss'
                                            in if is == (is `intersect` ss)
                                               then return is
                                               else fail $ "args " ++ commas (filter (`notElem` ss) is) ++ " are not static."

-- | Generalized Static Argument Transformation, which allows static arguments to be filtered.
staticArgPredR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c)
               => ([(Int, Var)] -> HermitM [Int]) -- ^ given list of static args and positions, decided which to transform
               -> Rewrite c HermitM CoreDef
staticArgPredR decide = prefixFailMsg "static-arg failed: " $ do
    Def f rhs <- idR
    let (bnds, body) = collectBinders rhs
    guardMsg (notNull bnds) "rhs is not a function"
    contextonlyT $ \ c -> do
        let bodyContext = foldl (flip addLambdaBinding) c bnds

        callPats <- apply (callsT (var2THName f) (callT >>> arr snd)) bodyContext (ExprCore body)
        let argExprs = transpose callPats
            numCalls = length callPats
            allBinds = zip [0..] bnds

            staticBinds = [ (i,b) | ((i,b),exprs) <- zip allBinds $ argExprs ++ repeat []
                                  , length exprs == numCalls && isStatic b exprs ]
                                    -- ensure argument is present in every call (partial applications boo)

            isStatic _ []                          = True  -- all were static
            isStatic b ((Var b'):es)               | b == b' = isStatic b es
            isStatic b ((Type (TyVarTy v)):es)     | b == v  = isStatic b es
            isStatic b ((Coercion (CoVarCo v)):es) | b == v  = isStatic b es
            isStatic _ _                           = False -- not a simple repass, so dynamic

        chosen <- decide staticBinds
        let choices = map fst staticBinds
        guardMsg (notNull chosen) "no arguments selected for transformation."
        guardMsg (all (`elem` choices) chosen)
            $ "args " ++ commas choices ++ " are static, but " ++ commas chosen ++ " were selected."

        let (chosenBinds, dynBinds) = partition ((`elem` chosen) . fst) allBinds
            (ps, dbnds) = unzip dynBinds
            unboundTys = concat [ [ (i,i') | (i',b') <- dynBinds, i' < i , b' `elem` fvs ]
                                | (i,b) <- chosenBinds, let fvs = varSetElems (varTypeTyVars b) ]

        guardMsg (null unboundTys)
            $ "type variables in args " ++ commas (nub $ map fst unboundTys) ++ " would become unbound unless args "
              ++ commas (nub $ map snd unboundTys) ++ " are included in the transformation."

        wkr <- newIdH (var2String f ++ "'") (exprType (mkCoreLams dbnds body))

        let replaceCall :: Monad m => Rewrite c m CoreExpr
            replaceCall = do
                (_,exprs) <- callT
                return $ mkApps (Var wkr) [ e | (p,e) <- zip [0..] exprs, (p::Int) `elem` ps ]

        ExprCore body' <- apply (callsR (var2THName f) replaceCall) bodyContext (ExprCore body)

        return $ Def f $ mkCoreLams bnds $ Let (Rec [(wkr, mkCoreLams dbnds body')])
                                             $ mkApps (Var wkr) (varsToCoreExprs dbnds)

commas :: Show a => [a] -> String
commas = intercalate "," . map show
