{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins as GHC hiding (varName)

import Control.Applicative
import Control.Arrow
import Control.Monad

import Data.List(intercalate,intersect)

import Language.HERMIT.Context
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Utils
import Language.HERMIT.Primitive.Local
import Language.HERMIT.Primitive.Local.Case
import Language.HERMIT.Primitive.Local.Let
import Language.HERMIT.Primitive.Inline
-- import Language.HERMIT.Primitive.Debug

import qualified Language.Haskell.TH as TH

-- import Debug.Trace
import MonadUtils (MonadIO) -- GHC's MonadIO


externals ::  [External]
externals = map ((.+ Experiment) . (.+ TODO))
         [ external "info" (info :: TranslateH Core String)
                [ "tell me what you know about this expression or binding" ] .+ Unimplemented
         , external "expr-type" (promoteExprT exprTypeT :: TranslateH Core String)
                [ "display the type of this expression"]
         , external "test" (testQuery :: RewriteH Core -> TranslateH Core String)
                [ "determines if a rewrite could be successfully applied" ]
         , external "fix-intro" (promoteDefR fixIntro :: RewriteH Core)
                [ "rewrite a recursive binding into a non-recursive binding using fix" ]
         , external "fix-spec" (promoteExprR fixSpecialization :: RewriteH Core)
                [ "specialize a fix with a given argument"] .+ Shallow
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
                [ "innermost (unfold '. <+ beta-reduce-plus <+ safe-let-subst <+ case-reduce <+ dead-code-elimination)" ]
         , external "let-tuple" (promoteExprR . letTupleR :: TH.Name -> RewriteH Core)
                [ "let x = e1 in (let y = e2 in e) ==> let t = (e1,e2) in (let x = fst t in (let y = snd t in e))" ]
         , external "any-call" (withUnfold :: RewriteH Core -> RewriteH Core)
                [ "any-call (.. unfold command ..) applies an unfold commands to all applications"
                , "preference is given to applications with more arguments"
                ] .+ Deep
         , external "abstract" (promoteExprR . abstract :: TH.Name -> RewriteH Core)
                [ "Abstract over a variable using a lambda.",
                  "e  ==>  (\\ x -> e) x"
                ] .+ Shallow .+ Introduce .+ Context
         ]


isVar :: TH.Name -> TranslateH CoreExpr ()
isVar nm = varT (cmpTHName2Id nm) >>= guardM

simplifyR :: RewriteH Core
simplifyR = innermostR (promoteExprR (unfold (TH.mkName ".") <+ betaReducePlus <+ safeLetSubstR <+ caseReduce <+ dce))

-- This left for Neil's IFL presentation. letTupleR is the more general version.
letPairR :: TH.Name -> RewriteH CoreExpr
letPairR nm = do
    Let (NonRec x e1) (Let (NonRec y e2) e) <- idR
    ifM (letT (nonRecT (pure ()) const)
              (letT (nonRecT freeVarsT (flip const)) (pure ()) const)
              elem)
        (fail "'x' is used in 'e2'")
        (translate $ \ c _ -> do
              tupleConId <- findId c "(,)"
              fstId <- findId c "Data.Tuple.fst"
              sndId <- findId c "Data.Tuple.snd"
              let e1TyE = Type (exprType e1)
                  e2TyE = Type (exprType e2)
                  rhs = mkCoreApps (Var tupleConId) [e1TyE, e2TyE, e1, e2]
              letId <- newVarH (show nm) (exprType rhs)
              let fstE = mkCoreApps (Var fstId) [e1TyE, e2TyE, Var letId]
                  sndE = mkCoreApps (Var sndId) [e1TyE, e2TyE, Var letId]
              return $ Let (NonRec letId rhs)
                      $ Let (NonRec x fstE)
                       $ Let (NonRec y sndE) e)

letTupleR :: TH.Name -> RewriteH CoreExpr
letTupleR nm = translate $ \ c e -> do
    let collectLets :: CoreExpr -> ([(Id, CoreExpr)],CoreExpr)
        collectLets (Let (NonRec x e1) e2) = let (bs,expr) = collectLets e2
                                             in ((x,e1):bs, expr)
        collectLets expr = ([],expr)

        (bnds, body) = collectLets e

    guardMsg (length bnds > 1) "cannot tuple: need at least two nonrec lets"

    -- until we no longer need letPairR
    if length bnds == 2
      then apply (letPairR nm) c e
      else do
        -- check if tupling the bindings would cause unbound variables
        let (ids, rhss) = unzip bnds

        frees <- mapM (apply freeVarsT c) (drop 1 rhss)

        let used = concat $ zipWith intersect (map (flip take ids) [1..]) frees

        if null used
          then do
            tupleConId <- findId c $ "(" ++ replicate (length bnds - 1) ',' ++ ")"

            let rhs = mkCoreApps (Var tupleConId) $ map (Type . exprType) rhss ++ rhss
                varList = concat $ iterate (zipWith (flip (++)) $ repeat "0") $ map (:[]) ['a'..'z']
            dc <- maybe (fail "cannot find tuple datacon") return $ isDataConId_maybe tupleConId
            vs <- zipWithM newVarH varList $ dataConInstOrigArgTys dc $ map exprType rhss

            letId <- newVarH (show nm) (exprType rhs)
            return $ Let (NonRec letId rhs)
                     $ foldr (\ (i,(v,oe)) b -> Let (NonRec v (Case (Var letId) letId (exprType oe) [(DataAlt dc, vs, Var $ vs !! i)])) b)
                             body $ zip [0..] bnds
          else fail "cannot tuple: some bindings are used in the rhs of others"

-- Others
-- let v = E1 in E2 E3 <=> (let v = E1 in E2) E3
-- let v = E1 in E2 E3 <=> E2 (let v = E1 in E3)

-- A few Queries.

info :: TranslateH Core String
info = translate $ \ c core -> do
         dynFlags <- getDynFlags
         let pa       = "Path: " ++ show (contextPath c)
             node     = "Node: " ++ coreNode core
             con      = "Constructor: " ++ coreConstructor core
             bds      = "Bindings in Scope: " ++ (show $ map unqualifiedIdName $ listBindings c)
             expExtra = case core of
                          ExprCore e -> ["Type: " ++ showExprType dynFlags e] ++
                                        ["Free Variables: " ++ showVars dynFlags (coreExprFreeVars e)] ++
                                           case e of
                                             Var v -> ["Identifier Info: " ++ showIdInfo dynFlags v]
                                             _     -> []
                          _          -> []

         return (intercalate "\n" $ [pa,node,con,bds] ++ expExtra)

exprTypeT :: TranslateH CoreExpr String
exprTypeT = contextfreeT $ \ e -> do
    dynFlags <- getDynFlags
    return $ showExprType dynFlags e

showExprType :: DynFlags -> CoreExpr -> String
showExprType dynFlags = showPpr dynFlags . exprType

showIdInfo :: DynFlags -> Id -> String
showIdInfo dynFlags v = showSDoc dynFlags $ ppIdInfo v $ idInfo v

coreNode :: Core -> String
coreNode (ModGutsCore _) = "Module"
coreNode (ProgramCore _) = "Program"
coreNode (BindCore _)    = "Binding Group"
coreNode (DefCore _)     = "Recursive Definition"
coreNode (ExprCore _)    = "Expression"
coreNode (AltCore _)     = "Case Alternative"

coreConstructor :: Core -> String
coreConstructor (ModGutsCore _)    = "ModGuts"
coreConstructor (ProgramCore prog) = case prog of
                                       []    -> "[]"
                                       (_:_) -> "(:)"
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

findId :: (MonadUnique m, MonadIO m, MonadThings m, HasDynFlags m) => Context -> String -> m Id
findId c = findIdMG (hermitModGuts c)

findIdMG :: (MonadUnique m, MonadIO m, MonadThings m, HasDynFlags m) => ModGuts -> String -> m Id
findIdMG modguts nm =
    case filter isValName $ findNameFromTH (mg_rdr_env modguts) $ TH.mkName nm of
        []  -> fail $ "cannot find " ++ nm
        [n] -> lookupId n
        ns  -> do dynFlags <- getDynFlags
                  fail $ "too many " ++ nm ++ " found:\n" ++ intercalate ", " (map (showPpr dynFlags) ns)

-- |  f = e   ==>   f = fix (\ f -> e)
fixIntro :: RewriteH CoreDef
fixIntro = prefixFailMsg "Fix introduction failed: " $
           do (c, Def f e) <- exposeT
              constT $ do fixId <- findId c "Data.Function.fix"
                          f' <- cloneIdH id f
                          let coreFix = App (App (Var fixId) (Type (idType f)))
                              emptySub = mkEmptySubst (mkInScopeSet (exprFreeVars e))
                              sub      = extendSubst emptySub f (Var f')
                          return $ Def f (coreFix (Lam f' (substExpr (text "fixIntro") sub e)))

-- ironically, this is an instance of worker/wrapper itself.

fixSpecialization :: RewriteH CoreExpr
fixSpecialization = do
        fixId <- translate $ \ c _ -> findId c "Data.Function.fix"

        -- fix (t::*) (f :: t -> t) (a :: t) :: t
        App (App (App (Var fx) (Type _)) _) _ <- idR

        guardMsg (fx == fixId) "fixSpecialization only works on fix"

        let rr :: RewriteH CoreExpr
            rr = multiEtaExpand [TH.mkName "f",TH.mkName "a"]

            sub :: RewriteH Core
            sub = pathR [0,1] (promoteR rr)
        -- be careful this does not loop (it should not)
        extractR sub >>> fixSpecialization'


fixSpecialization' :: RewriteH CoreExpr
fixSpecialization' = do
        -- In normal form now
        App (App (App (Var fx) (Type t))
                 (Lam _ (Lam v2 (App (App e _) _a2)))
            )
            a <- idR

        let t' = case a of
                   Type t2  -> applyTy t t2
                   (Var x) | isTyVar x -> applyTy t (mkTyVarTy x)
--                   Var  a2  -> mkAppTy t (exprType t2)
--                   mkAppTy t t'


        -- TODO: t2' isn't used anywhere -- which means that a2 is never used ???
--        let t2' = case a2 of
--                   Type t2  -> applyTy t t2
--                   Var  a2  -> mkAppTy t (exprType t2)
--                   mkAppTy t t'


        v3 <- constT $ newVarH "f" t' -- (funArgTy t')
        v4 <- constT $ newTypeVarH "a" (tyVarKind v2)

         -- f' :: \/ a -> T [a] -> (\/ b . T [b])
        let f' = Lam v4  (Cast (Var v3)
                               (mkUnsafeCo t' (applyTy t (mkTyVarTy v4))))
        let e' = Lam v3 (App (App e f') a)

        return $ App (App (Var fx) (Type t')) e'


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
                  guardMsg (nm `cmpTHName2Id` v) $ "could not find name " ++ show nm
                  guardMsg (not $ null args) $ "no argument for " ++ show nm
                  guardMsg (all isTypeArg $ init args) $ "initial arguments are not type arguments for " ++ show nm
                  case last args of
                     Case {} -> caseFloatArg
                     Let {}  -> letFloatArg
                     _       -> fail "argument is not a Case or Let."
          _ -> fail "no function to match."

-- | Abstract over a variable using a lambda.
--   e  ==>  (\ x. e) x
abstract :: TH.Name -> RewriteH CoreExpr
abstract nm = prefixFailMsg "abstraction failed: " $
    do (c,e) <- exposeT
       let name = TH.nameBase nm
       case filter (cmpTHName2Id nm) (listBindings c) of
         []         -> fail $ name ++ " is not in scope."
         [v]        -> return (App (Lam v e) (Var v)) -- There might be issues if "v" is a type variable, I'm not sure.
         _ : _ : _  -> fail $ "multiple variables named " ++ name ++ " in scope."
