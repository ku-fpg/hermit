-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins as GHC hiding (varName)

import Control.Applicative
import Control.Arrow
import Control.Monad

import Data.List(intercalate,intersect)

import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Local
import Language.HERMIT.Primitive.Inline
-- import Language.HERMIT.Primitive.Debug

import qualified Language.Haskell.TH as TH


externals ::  [External]
externals = map ((.+ Experiment) . (.+ TODO))
         [ external "info" (info :: TranslateH Core String)
                [ "tell me what you know about this expression or binding" ]
         -- , external "expr-type" (promoteExprT exprTypeT :: TranslateH Core String)
         --        [ "display the type of this expression"]
         , external "test" (testQuery :: RewriteH Core -> TranslateH Core String)
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
         ]


isVar :: TH.Name -> TranslateH CoreExpr ()
isVar nm = varT (cmpTHName2Id nm) >>= guardM

simplifyR :: RewriteH Core
simplifyR = setFailMsg "Simplify failed: nothing to simplify." $
            innermostR (promoteExprR (unfold (TH.mkName ".") <+ betaReducePlus <+ safeLetSubstR <+ caseReduce <+ letElim))


collectLets :: CoreExpr -> ([(Id, CoreExpr)],CoreExpr)
collectLets (Let (NonRec x e1) e2) = let (bs,expr) = collectLets e2 in ((x,e1):bs, expr)
collectLets expr                   = ([],expr)

-- | Combine nested non-recursive lets into case of a tuple.
letTupleR :: TH.Name -> RewriteH CoreExpr
letTupleR nm = prefixFailMsg "Let-tuple failed: " $
  do (bnds, body) <- arr collectLets
     guardMsg (length bnds > 1) "at least two non-recursive lets required."

      -- check if tupling the bindings would cause unbound variables
     let (ids, rhss) = unzip bnds
         rhsTypes    = map exprType rhss
         frees       = mapM coreExprFreeVars (drop 1 rhss)
         used        = concat $ zipWith intersect (map (`take` ids) [1..]) frees

     if null used
       then do tupleConId <- findIdT $ TH.mkName $ "(" ++ replicate (length bnds - 1) ',' ++ ")"
               let rhs     = mkCoreApps (Var tupleConId) $ map Type rhsTypes ++ rhss
                   varList = concat $ iterate (zipWith (flip (++)) $ repeat "0") $ map (:[]) ['a'..'z']
               case isDataConId_maybe tupleConId of
                 Nothing -> fail "cannot find tuple data constructor."
                 Just dc -> constT $ do vs    <- zipWithM newVarH varList $ dataConInstOrigArgTys dc rhsTypes
                                        letId <- newVarH (show nm) (exprType rhs)
                                        return $ Let (NonRec letId rhs)
                                           $ foldr (\ (i,(v,oe)) b -> Let (NonRec v (Case (Var letId) letId (exprType oe) [(DataAlt dc, vs, Var $ vs !! i)])) b)
                                               body $ zip [0..] bnds

       else fail "some bindings are used in the rhs of others"

-- Others
-- let v = E1 in E2 E3 <=> (let v = E1 in E2) E3
-- let v = E1 in E2 E3 <=> E2 (let v = E1 in E3)


-- letTupleR :: TH.Name -> RewriteH CoreExpr
-- letTupleR nm = translate $ \ c e -> do
--     let collectLets :: CoreExpr -> ([(Id, CoreExpr)],CoreExpr)
--         collectLets (Let (NonRec x e1) e2) = let (bs,expr) = collectLets e2
--                                              in ((x,e1):bs, expr)
--         collectLets expr = ([],expr)

--         (bnds, body) = collectLets e

--     guardMsg (length bnds > 1) "cannot tuple: need at least two nonrec lets"

--     -- check if tupling the bindings would cause unbound variables
--     let (ids, rhss) = unzip bnds
--     frees <- mapM (apply freeVarsT c) (drop 1 rhss)
--     let used = concat $ zipWith intersect (map (`take` ids) [1..]) frees
--     if null used
--       then do
--         tupleConId <- findId c $ "(" ++ replicate (length bnds - 1) ',' ++ ")"

--         let rhs = mkCoreApps (Var tupleConId) $ map (Type . exprType) rhss ++ rhss
--             varList = concat $ iterate (zipWith (flip (++)) $ repeat "0") $ map (:[]) ['a'..'z']
--         dc <- maybe (fail "cannot find tuple datacon") return $ isDataConId_maybe tupleConId
--         vs <- zipWithM newVarH varList $ dataConInstOrigArgTys dc $ map exprType rhss

--         letId <- newVarH (show nm) (exprType rhs)
--         return $ Let (NonRec letId rhs)
--                  $ foldr (\ (i,(v,oe)) b -> Let (NonRec v (Case (Var letId) letId (exprType oe) [(DataAlt dc, vs, Var $ vs !! i)])) b)
--                          body $ zip [0..] bnds
--       else fail "cannot tuple: some bindings are used in the rhs of others"

-- A few Queries.

info :: TranslateH Core String
info = translate $ \ c core -> do
         dynFlags <- getDynFlags
         let pa       = "Path: " ++ show (contextPath c)
             node     = "Node: " ++ coreNode core
             con      = "Constructor: " ++ coreConstructor core
             bds      = "Bindings in Scope: " ++ show (map unqualifiedIdName $ boundIds c)
             expExtra = case core of
                          ExprCore e -> ["Type: " ++ showExprType dynFlags e] ++
                                        ["Free Variables: " ++ showVars (coreExprFreeVars e)] ++
                                           case e of
                                             Var v -> ["Identifier Info: " ++ showIdInfo dynFlags v]
                                             _     -> []
                          _          -> []

         return (intercalate "\n" $ [pa,node,con,bds] ++ expExtra)

-- Subsumed by "info".
-- exprTypeT :: TranslateH CoreExpr String
-- exprTypeT = contextfreeT $ \ e -> do
--     dynFlags <- getDynFlags
--     return $ showExprType dynFlags e

showExprType :: DynFlags -> CoreExpr -> String
showExprType dynFlags = showPpr dynFlags . exprType

showIdInfo :: DynFlags -> Id -> String
showIdInfo dynFlags v = showSDoc dynFlags $ ppIdInfo v $ idInfo v

coreNode :: Core -> String
coreNode (ModGutsCore _) = "Module"
coreNode (ProgCore _)    = "Program"
coreNode (BindCore _)    = "Binding Group"
coreNode (DefCore _)     = "Recursive Definition"
coreNode (ExprCore _)    = "Expression"
coreNode (AltCore _)     = "Case Alternative"

coreConstructor :: Core -> String
coreConstructor (ModGutsCore _)    = "ModGuts"
coreConstructor (ProgCore prog)    = case prog of
                                       ProgNil      -> "ProgNil"
                                       ProgCons _ _ -> "ProgCons"
coreConstructor (BindCore bnd)     = case bnd of
                                       Rec _      -> "Rec"
                                       NonRec _ _ -> "NonRec"
coreConstructor (DefCore _)        = "Def"
coreConstructor (AltCore _)        = "(,,)"
coreConstructor (ExprCore expr)    = case expr of
                                       Var _        -> "Var"
                                       Type _       -> "Type"
                                       Lit _        -> "Lit"
                                       App _ _      -> "App"
                                       Lam _ _      -> "Lam"
                                       Let _ _      -> "Let"
                                       Case _ _ _ _ -> "Case"
                                       Cast _ _     -> "Cast"
                                       Tick _ _     -> "Tick"
                                       Coercion _   -> "Coercion"

testQuery :: RewriteH Core -> TranslateH Core String
testQuery r = f <$> testM r
  where
    f True  = "Rewrite would succeed."
    f False = "Rewrite would fail."


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


-- | Push a function through a Case or Let expression.
--   Unsafe if the function is not strict.
push :: TH.Name -> RewriteH CoreExpr
push nm = prefixFailMsg "push failed: " $
     do e <- idR
        case collectArgs e of
          (Var v,args) -> do
                  guardMsg (nm `cmpTHName2Id` v) $ "cannot find name " ++ show nm
                  guardMsg (not $ null args) $ "no argument for " ++ show nm
                  guardMsg (all isTypeArg $ init args) $ "initial arguments are not type arguments for " ++ show nm
                  case last args of
                     Case {} -> caseFloatArg
                     Let {}  -> letFloatArg
                     _       -> fail "argument is not a Case or Let."
          _ -> fail "no function to match."
