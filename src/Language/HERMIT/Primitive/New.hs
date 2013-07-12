{-# LANGUAGE FlexibleContexts, ScopedTypeVariables, MultiWayIf #-}

-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins as GHC hiding (varName)

import Control.Arrow

import Data.List(transpose)

import Language.HERMIT.Context
import Language.HERMIT.Core
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC
import Language.HERMIT.ParserCore

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Local
import Language.HERMIT.Primitive.Unfold
-- import Language.HERMIT.Primitive.Debug

import qualified Language.Haskell.TH as TH


externals ::  [External]
externals = map ((.+ Experiment) . (.+ TODO))
         [ external "var" (promoteExprT . isVar :: TH.Name -> TranslateH Core ())
                [ "var '<v> returns successfully for variable v, and fails otherwise.",
                  "Useful in combination with \"when\", as in: when (var v) r" ] .+ Predicate
         , external "simplify" (simplifyR :: RewriteH Core)
                [ "innermost (unfold 'id <+ unfold '$ <+ unfold '. <+ beta-reduce-plus <+ safe-let-subst <+ case-reduce <+ let-elim)" ] .+ Bash
         , external "static-arg" (promoteDefR staticArg :: RewriteH Core)
                [ "perform the static argument transformation on a recursive function" ]
         , external "unsafe-replace" (promoteExprR . unsafeReplace :: CoreString -> RewriteH Core)
                [ "replace the currently focused expression with a new expression" ] .+ Unsafe
         , external "unsafe-replace" (promoteExprR . unsafeReplaceStash :: String -> RewriteH Core)
                [ "replace the currently focused expression with an expression from the stash"
                , "DOES NOT ensure expressions have the same type, or that free variables in the replacement expression are in scope" ] .+ Unsafe
         , external "prog-nonrec-intro" ((\ nm core -> promoteProgR $ progNonRecIntroR (show nm) core) :: TH.Name -> CoreString -> RewriteH Core)
                [ "Introduce a new top-level definition."
                , "prog-nonrec-into 'v [| e |]"
                , "prog ==> ProgCons (v = e) prog" ] .+ Introduce .+ Shallow
         , external "let-nonrec-intro" ((\ nm core -> promoteExprR $ letNonRecIntroR (show nm) core) :: TH.Name -> CoreString -> RewriteH Core)
                [ "Introduce a new definition as a non-recursive let binding."
                , "let-nonrec-intro 'v [| e |]"
                , "body ==> let v = e in body" ] .+ Introduce .+ Shallow
         ]

------------------------------------------------------------------------------------------------------

-- TODO:  We might not want to match on TyVars and CoVars here.
-- Probably better to have another predicate that operates on CoreTC, that way it can reach TyVars buried within types.
-- But given the current setup (using Core for most things), changing "var" to operate on CoreTC would make it incompatible with other combinators.
-- I'm not sure how to fix the current setup though.
-- isVar :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => TH.Name -> Translate c m CoreExpr ()
-- isVar nm = (varT matchName <+ typeT (tyVarT matchName) <+ coercionT (coVarCoT matchName))
--                  >>= guardM
--   where
--     matchName :: Monad m => Translate c m Var Bool
--     matchName = arr (cmpTHName2Var nm)

-- TODO: there might be a better module for this

-- | Test if the current expression is an identifier matching the given name.
isVar :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => TH.Name -> Translate c m CoreExpr ()
isVar nm = varT (arr $ cmpTHName2Var nm) >>= guardM

------------------------------------------------------------------------------------------------------

simplifyR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM Core
simplifyR = setFailMsg "Simplify failed: nothing to simplify." $
    innermostR (promoteExprR (unfoldNameR (TH.mkName "$")
                           <+ unfoldNameR (TH.mkName ".")
                           <+ unfoldNameR (TH.mkName "id")
                           <+ betaReducePlus
                           <+ safeLetSubstR
                           <+ caseReduce
                           <+ letElim))

staticArg :: forall c. (ExtendPath c Crumb, AddBindings c) => Rewrite c HermitM CoreDef
staticArg = prefixFailMsg "static-arg failed: " $ do
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

------------------------------------------------------------------------------------------------------

-- The types of these can probably be generalised after the Core Parser is generalised.

parseCoreExprT :: CoreString -> TranslateH a CoreExpr
parseCoreExprT = contextonlyT . parseCore

unsafeReplace :: CoreString -> RewriteH CoreExpr
unsafeReplace core =
    translate $ \ c e -> do
        e' <- parseCore core c
        guardMsg (eqType (exprType e) (exprType e')) "expression types differ."
        return e'

unsafeReplaceStash :: String -> RewriteH CoreExpr
unsafeReplaceStash label = prefixFailMsg "unsafe-replace failed: " $
    contextfreeT $ \ e -> do
        Def _ rhs <- lookupDef label
        guardMsg (eqType (exprType e) (exprType rhs)) "expression types differ."
        return rhs

-- | @prog@ ==> @'ProgCons' (v = e) prog@
progNonRecIntroR :: String -> CoreString -> RewriteH CoreProg
progNonRecIntroR nm expr =
  do e <- parseCoreExprT expr
     guardMsg (not $ isTyCoArg e) "Top-level type or coercion definitions are prohibited."
     -- TODO: if e is not type-correct, then exprType will crash.
     --       Proposal: parseCore should check that its result is (locally) well-typed
     contextfreeT $ \ prog -> do i <- newIdH nm (exprType e)
                                 return $ ProgCons (NonRec i e) prog

-- | @body@ ==> @let v = e in body@
letNonRecIntroR :: String -> CoreString -> RewriteH CoreExpr
letNonRecIntroR nm expr =
  do e <- parseCoreExprT expr
     -- TODO: if e is not type-correct, then exprTypeOrKind will crash.
     --       Proposal: parseCore should check that its result is (locally) well-typed
     contextfreeT $ \ body -> do let tyk = exprKindOrType e
                                 v <- if | isTypeArg e  -> newTyVarH nm tyk
                                         | isCoArg e    -> newCoVarH nm tyk
                                         | otherwise    -> newIdH nm tyk
                                 return $ Let (NonRec v e) body

------------------------------------------------------------------------------------------------------
