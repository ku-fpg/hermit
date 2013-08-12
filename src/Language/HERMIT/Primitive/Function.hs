{-# LANGUAGE FlexibleContexts, RankNTypes #-}
module Language.HERMIT.Primitive.Function
    ( externals
    , staticArgR
    ) where

import GhcPlugins as GHC hiding (varName)

import Control.Arrow

import Data.List(transpose)

import Language.HERMIT.Context
import Language.HERMIT.Core
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC

import Language.HERMIT.Primitive.Common

externals ::  [External]
externals =
    [ external "static-arg" (promoteDefR staticArgR :: RewriteH Core)
        [ "perform the static argument transformation on a recursive function" ]
    ]

------------------------------------------------------------------------------------------------------

staticArgR :: forall c. (ExtendPath c Crumb, AddBindings c) => Rewrite c HermitM CoreDef
staticArgR = prefixFailMsg "static-arg failed: " $ do
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
                                       , length exprs /= numCalls || isDynamic b exprs
                                       ]

            isDynamic _ []                      = False     -- all were static, so static
            isDynamic b ((Var b'):es)           | b == b' = isDynamic b es
            isDynamic b ((Type (TyVarTy v)):es) | b == v  = isDynamic b es
            isDynamic _ _                       = True      -- not a simple repass, so dynamic

        wkr <- newIdH (var2String f ++ "'") (exprType (mkCoreLams dbnds body))

        let replaceCall :: Monad m => Rewrite c m CoreExpr
            replaceCall = do
                (_,exprs) <- callT
                return $ mkApps (Var wkr) [ e | (p,e) <- zip [0..] exprs, (p::Int) `elem` ps ]

        ExprCore body' <- apply (callsR (var2THName f) replaceCall) bodyContext (ExprCore body)

        return $ Def f $ mkCoreLams bnds $ Let (Rec [(wkr, mkCoreLams dbnds body')])
                                             $ mkApps (Var wkr) (varsToCoreExprs dbnds)

