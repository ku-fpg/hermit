{-# LANGUAGE FlexibleContexts, RankNTypes #-}
module HERMIT.Primitive.Function
    ( externals
    , staticArgR
    , staticArgPredR
    , staticArgTypesR
    )
where

import Control.Arrow

import Data.List(transpose)

import HERMIT.Context
import HERMIT.Core
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC

import HERMIT.Primitive.Common

externals ::  [External]
externals =
    [ external "static-arg" (promoteDefR staticArgR :: RewriteH Core)
        [ "perform the static argument transformation on a recursive function" ]
    , external "static-arg-types" (promoteDefR staticArgTypesR :: RewriteH Core)
        [ "perform the static argument transformation on a recursive function, only transforming type arguments" ]
    ]

------------------------------------------------------------------------------------------------------

staticArgR :: forall c. (ExtendPath c Crumb, AddBindings c) => Rewrite c HermitM CoreDef
staticArgR = staticArgPredR (const True)

staticArgTypesR :: forall c. (ExtendPath c Crumb, AddBindings c) => Rewrite c HermitM CoreDef
staticArgTypesR = staticArgPredR (isTyVar . snd)

staticArgPredR :: forall c. (ExtendPath c Crumb, AddBindings c) 
           => ((Int, Var) -> Bool) -- ^ if an arg is static, apply predicate to position and binder
                                   --   True = transform as if it is static
                                   --   False = consider arg to be dynamic
           -> Rewrite c HermitM CoreDef
staticArgPredR pr = prefixFailMsg "static-arg failed: " $ do
    Def f rhs <- idR
    let (bnds, body) = collectBinders rhs
    guardMsg (notNull bnds) "rhs is not a function"
    contextonlyT $ \ c -> do
        let bodyContext = foldl (flip addLambdaBinding) c bnds

        callPats <- apply (callsT (var2THName f) (callT >>> arr snd)) bodyContext (ExprCore body)
        let argExprs = transpose callPats
            numCalls = length callPats
            -- ensure argument is present in every call (partial applications boo)
            (ps,dbnds) = unzip [ (i,b) | (i,b,exprs) <- zip3 [0..] bnds $ argExprs ++ repeat []
                                       , length exprs /= numCalls || isDynamic i b exprs
                                       ]

            isDynamic i b []                      = not $ pr (i,b) -- all were static, so check predicate
            isDynamic i b ((Var b'):es)           | b == b' = isDynamic i b es
            isDynamic i b ((Type (TyVarTy v)):es) | b == v  = isDynamic i b es
            isDynamic _ _ _                       = True             -- not a simple repass, so dynamic

        wkr <- newIdH (var2String f ++ "'") (exprType (mkCoreLams dbnds body))

        let replaceCall :: Monad m => Rewrite c m CoreExpr
            replaceCall = do
                (_,exprs) <- callT
                return $ mkApps (Var wkr) [ e | (p,e) <- zip [0..] exprs, (p::Int) `elem` ps ]

        ExprCore body' <- apply (callsR (var2THName f) replaceCall) bodyContext (ExprCore body)

        return $ Def f $ mkCoreLams bnds $ Let (Rec [(wkr, mkCoreLams dbnds body')])
                                             $ mkApps (Var wkr) (varsToCoreExprs dbnds)

