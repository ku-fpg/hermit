-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins as GHC hiding (varName)

import Control.Applicative
import Control.Arrow

import Data.List(intersect,transpose)

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
-- import Language.HERMIT.Primitive.Debug

import qualified Language.Haskell.TH as TH


externals ::  [External]
externals = map ((.+ Experiment) . (.+ TODO))
         [ external "test" (testQuery :: RewriteH Core -> TranslateH Core String)
                [ "determines if a rewrite could be successfully applied" ]
         , external "cleanup-unfold" (promoteExprR cleanupUnfold :: RewriteH Core)
                [ "clean up immeduate nested fully-applied lambdas, from the bottom up"]
         , external "unfold" (promoteExprR . unfold :: TH.Name -> RewriteH Core)
                [ "inline a definition, and apply the arguments; tranditional unfold"]
         , external "push" (promoteExprR . push :: TH.Name -> RewriteH Core)
                [ "push a function <f> into argument."
                , "Unsafe if f is not strict." ] .+ PreCondition
                        -- TODO: does not work with rules with no arguments
         , external "unfold-rule" ((\ nm -> promoteExprR (rules nm >>> cleanupUnfold)) :: String -> RewriteH Core)
                [ "apply a named GHC rule" ]
         , external "var" (promoteExprT . isVar :: TH.Name -> TranslateH Core ())
                 [ "var '<v> returns successfully for variable v, and fails otherwise.",
                   "Useful in combination with \"when\", as in: when (var v) r" ] .+ Predicate
         , external "simplify" (simplifyR :: RewriteH Core)
                [ "innermost (unfold '. <+ beta-reduce-plus <+ safe-let-subst <+ case-reduce <+ dead-let-elimination)" ]
         , external "let-tuple" (promoteExprR . letTupleR :: TH.Name -> RewriteH Core)
                [ "let x = e1 in (let y = e2 in e) ==> let t = (e1,e2) in (let x = fst t in (let y = snd t in e))" ]
         , external "any-call" (withUnfold :: RewriteH Core -> RewriteH Core)
                [ "any-call (.. unfold command ..) applies an unfold commands to all applications"
                , "preference is given to applications with more arguments"
                ] .+ Deep
         , external "static-arg" (promoteDefR staticArg :: RewriteH Core)
                [ "perform the static argument transformation on a recursive function" ]
         , external "unsafe-replace" (promoteExprR . unsafeReplace :: CoreString -> RewriteH Core)
                [ "replace the currently focused expression with a new expression" ]
         ]

------------------------------------------------------------------------------------------------------

-- TODO: what about Type constructors around TyVars?
isVar :: TH.Name -> TranslateH CoreExpr ()
isVar nm = varT (cmpTHName2Var nm) >>= guardM

------------------------------------------------------------------------------------------------------

simplifyR :: RewriteH Core
simplifyR = setFailMsg "Simplify failed: nothing to simplify." $
            innermostR (promoteExprR (unfold (TH.mkName ".") <+ betaReducePlus <+ safeLetSubstR <+ caseReduce <+ letElim))


collectLets :: CoreExpr -> ([(Var, CoreExpr)],CoreExpr)
collectLets (Let (NonRec x e1) e2) = let (bs,expr) = collectLets e2 in ((x,e1):bs, expr)
collectLets expr                   = ([],expr)

-- | Combine nested non-recursive lets into case of a tuple.
letTupleR :: TH.Name -> RewriteH CoreExpr
letTupleR nm = prefixFailMsg "Let-tuple failed: " $
  do (bnds, body) <- arr collectLets
     let numBnds = length bnds
     guardMsg (numBnds > 1) "at least two non-recursive let bindings required."

     let (vs, rhss)  = unzip bnds
     guardMsg (all isId vs) "cannot tuple type variables." -- TODO: it'd be better if collectLets stopped on reaching a TyVar

     -- check if tupling the bindings would cause unbound variables
     let
         rhsTypes = map exprType rhss
         frees    = map coreExprFreeVars (drop 1 rhss)
         used     = concat $ zipWith intersect (map (`take` vs) [1..]) frees
     if null used
       then do tupleConId <- findIdT $ TH.mkName $ "(" ++ replicate (numBnds - 1) ',' ++ ")"
               case isDataConId_maybe tupleConId of
                 Nothing -> fail "cannot find tuple data constructor."
                 Just dc -> let rhs = mkCoreApps (Var tupleConId) $ map Type rhsTypes ++ rhss
                             in constT $ do wild <- newIdH (show nm) (exprType rhs)
                                            return $ Case rhs wild (exprType body) [(DataAlt dc, vs, body)]

       else fail $ "the following bound variables are used in subsequent bindings: " ++ showVars used

-- Others
-- let v = E1 in E2 E3 <=> (let v = E1 in E2) E3
-- let v = E1 in E2 E3 <=> E2 (let v = E1 in E3)

staticArg :: RewriteH CoreDef
staticArg = prefixFailMsg "static-arg failed: " $ do
    Def f rhs <- idR
    let (bnds, body) = collectBinders rhs
    guardMsg (notNull bnds) "rhs is not a function"
    c <- contextT
    constT $ do
        let bodyContext = foldl (flip addLambdaBinding) c bnds

        callPats <- apply (callsT (var2THName f) (collectArgsT >>> arr snd)) bodyContext (ExprCore body)
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

        let replaceCall :: RewriteH CoreExpr
            replaceCall = do
                (_,exprs) <- collectArgsT
                return $ mkApps (Var wkr) [ e | (p,e) <- zip [0..] exprs, (p::Int) `elem` ps ]

        ExprCore body' <- apply (callsR (var2THName f) replaceCall) bodyContext (ExprCore body)

        return $ Def f $ mkCoreLams bnds $ Let (Rec [(wkr, mkCoreLams dbnds body')])
                                             $ mkApps (Var wkr) (varsToCoreExprs dbnds)

-- | Like GHC's collectArgs, but fails if not an application
collectArgsT :: TranslateH CoreExpr (CoreExpr, [CoreExpr])
collectArgsT = do
    App {} <- idR
    arr collectArgs

-- | Succeeds if we are looking at an application of given function
callG :: TH.Name -> TranslateH CoreExpr ()
callG nm = prefixFailMsg "callG failed: " $ do
    (Var i,_) <- collectArgsT
    guardMsg (cmpTHName2Var nm i) $ "not a call to " ++ show nm
    return ()

-- | Apply a rewrite to all applications of a given function in a top-down manner, pruning on success.
callsR :: TH.Name -> RewriteH CoreExpr -> RewriteH Core
callsR nm rr = prunetdR (promoteExprR $ callG nm >> rr)

-- | Apply a translate to all applications of a given function in a top-down manner,
--   pruning on success, collecting the results.
callsT :: TH.Name -> TranslateH CoreExpr b -> TranslateH Core [b]
callsT nm t = collectPruneT (promoteExprT $ callG nm >> t)

------------------------------------------------------------------------------------------------------

testQuery :: RewriteH Core -> TranslateH Core String
testQuery r = f <$> testM r
  where
    f True  = "Rewrite would succeed."
    f False = "Rewrite would fail."

------------------------------------------------------------------------------------------------------

-- | cleanupUnfold cleans a unfold operation
--  (for example, an inline or rule application)
-- It is used at the level of the top-redex.
cleanupUnfold :: RewriteH CoreExpr
cleanupUnfold = betaReducePlus >>> safeLetSubstPlusR

unfold :: TH.Name -> RewriteH CoreExpr
unfold nm = translate $ \ env e0 -> do
        let n = appCount e0
        let sub :: RewriteH Core
            sub = pathR (replicate n 0) (promoteR $ inlineName nm)

            sub2 :: RewriteH CoreExpr
            sub2 = extractR sub

        e1 <- apply sub2 env e0

        -- only cleanup if 1 or more arguments
        if n > 0 then apply cleanupUnfold env e1
                 else return e1

-- match in a top-down manner,
withUnfold :: RewriteH Core -> RewriteH Core
withUnfold rr = prefixFailMsg "any-call failed: " $
                readerT $ \ e -> case e of
        ExprCore (App {}) -> childR 1 rec >+> (rr <+ childR 0 rec)
        ExprCore (Var {}) -> rr
        _                 -> anyR rec
   where

        rec :: RewriteH Core
        rec = withUnfold rr

------------------------------------------------------------------------------------------------------

-- | Push a function through a Case or Let expression.
--   Unsafe if the function is not strict.
push :: TH.Name -> RewriteH CoreExpr
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

unsafeReplace :: CoreString -> RewriteH CoreExpr
unsafeReplace = contextonlyT . parseCore . unCoreString
