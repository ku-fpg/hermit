{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins as GHC hiding (varName)

import Control.Arrow
import Control.Monad (liftM)

import Data.List(transpose)
import Data.Set (intersection, unions, fromList, toList)
import qualified Data.Set as S

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
import Language.HERMIT.Primitive.Inline
import Language.HERMIT.Primitive.Unfold
-- import Language.HERMIT.Primitive.Debug

import qualified Language.Haskell.TH as TH


externals ::  [External]
externals = map ((.+ Experiment) . (.+ TODO))
         [ external "test" (testQuery :: RewriteH Core -> TranslateH Core String)
                [ "determines if a rewrite could be successfully applied" ]
         , external "push" (promoteExprR . push :: TH.Name -> RewriteH Core)
                [ "push a function <f> into argument."
                , "Unsafe if f is not strict." ] .+ PreCondition
         , external "var" (promoteExprT . isVar :: TH.Name -> TranslateH Core ())
                 [ "var '<v> returns successfully for variable v, and fails otherwise.",
                   "Useful in combination with \"when\", as in: when (var v) r" ] .+ Predicate
         , external "simplify" (simplifyR :: RewriteH Core)
                [ "innermost (unfold 'id <+ unfold '$ <+ unfold '. <+ beta-reduce-plus <+ safe-let-subst <+ case-reduce <+ dead-let-elimination)" ] .+ Bash
         , external "let-tuple" (promoteExprR . letTupleR :: TH.Name -> RewriteH Core)
                [ "let x = e1 in (let y = e2 in e) ==> let t = (e1,e2) in (let x = fst t in (let y = snd t in e))" ]
         , external "any-call" (anyCallR :: RewriteH Core -> RewriteH Core)
                [ "any-call (.. unfold command ..) applies an unfold commands to all applications"
                , "preference is given to applications with more arguments"
                ] .+ Deep
         , external "static-arg" (promoteDefR staticArg :: RewriteH Core)
                [ "perform the static argument transformation on a recursive function" ]
         , external "unsafe-replace" (promoteExprR . unsafeReplace :: CoreString -> RewriteH Core)
                [ "replace the currently focused expression with a new expression" ] .+ Unsafe
         , external "unsafe-replace" (promoteExprR . unsafeReplaceStash :: String -> RewriteH Core)
                [ "replace the currently focused expression with an expression from the stash"
                , "DOES NOT ensure expressions have the same type, or that free variables in the replacement expression are in scope" ] .+ Unsafe
         , external "inline-all" (inlineAll :: [TH.Name] -> RewriteH Core)
                [ "inline all named functions in a bottom-up manner" ]
         ]

------------------------------------------------------------------------------------------------------

isVar :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => TH.Name -> Translate c m CoreExpr ()
isVar nm = let matchName = arr (cmpTHName2Var nm)
            in (varT matchName <+ typeT (tyVarT matchName)) >>= guardM

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

collectLets :: CoreExpr -> ([(Var, CoreExpr)],CoreExpr)
collectLets (Let (NonRec x e1) e2) = let (bs,expr) = collectLets e2 in ((x,e1):bs, expr)
collectLets expr                   = ([],expr)

-- | Combine nested non-recursive lets into case of a tuple.
letTupleR :: TH.Name -> Rewrite c HermitM CoreExpr
letTupleR nm = prefixFailMsg "Let-tuple failed: " $
  do (bnds, body) <- arr collectLets
     let numBnds = length bnds
     guardMsg (numBnds > 1) "at least two non-recursive let bindings required."

     let (vs, rhss)  = unzip bnds
     guardMsg (all isId vs) "cannot tuple type variables." -- TODO: it'd be better if collectLets stopped on reaching a TyVar

     -- check if tupling the bindings would cause unbound variables
     let
         frees    = map coreExprFreeVars (drop 1 rhss)
         used     = unions $ zipWith intersection (map (fromList . (`take` vs)) [1..]) frees
     if S.null used
       then let rhs = mkCoreTup rhss
            in constT $ do wild <- newIdH (show nm) (exprType rhs)
                           return $ mkSmallTupleCase vs body wild rhs

       else fail $ "the following bound variables are used in subsequent bindings: " ++ showVars (toList used)

-- Others
-- let v = E1 in E2 E3 <=> (let v = E1 in E2) E3
-- let v = E1 in E2 E3 <=> E2 (let v = E1 in E3)

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

testQuery :: MonadCatch m => Rewrite c m Core -> Translate c m Core String
testQuery r = f `liftM` testM r
  where
    f True  = "Rewrite would succeed."
    f False = "Rewrite would fail."

------------------------------------------------------------------------------------------------------

-- match in a top-down manner,
anyCallR :: forall c m. (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Rewrite c m Core -> Rewrite c m Core
anyCallR rr = prefixFailMsg "any-call failed: " $
              readerT $ \ e -> case e of
        ExprCore (App {}) -> childR App_Arg rec >+> (rr <+ childR App_Fun rec)
        ExprCore (Var {}) -> rr
        _                 -> anyR rec
   where

        rec :: Rewrite c m Core
        rec = anyCallR rr

------------------------------------------------------------------------------------------------------

-- | Push a function through a Case or Let expression.
--   Unsafe if the function is not strict.
push :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => TH.Name -> Rewrite c HermitM CoreExpr
push nm = prefixFailMsg "push failed: " $
     do e <- idR
        case collectArgs e of
          (Var v,args) -> do
                  guardMsg (nm `cmpTHName2Var` v) $ "cannot find name " ++ show nm
                  guardMsg (not $ null args) $ "no argument for " ++ show nm
                  guardMsg (all isTypeArg $ init args) $ "initial arguments are not type arguments for " ++ show nm
                  case last args of
                     Case {} -> caseFloatArg
                     Let {}  -> letFloatArg
                     _       -> fail "argument is not a Case or Let."
          _ -> fail "no function to match."

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

------------------------------------------------------------------------------------------------------

inlineAll :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => [TH.Name] -> Rewrite c HermitM Core
inlineAll = innermostR . foldr (\ nm rr -> promoteExprR (inlineName nm) <+ rr) (fail "inline-all: nothing to do")

------------------------------------------------------------------------------------------------------
