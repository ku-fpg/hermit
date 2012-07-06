{-# LANGUAGE TypeFamilies, FlexibleInstances, TemplateHaskell #-}

-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins as GHC hiding (varName)
--import Convert (thRdrNameGuesses)
-- import OccName(varName)

import Control.Applicative
import Control.Arrow

import Language.HERMIT.Context
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Local
import Language.HERMIT.Primitive.Local.Case
import Language.HERMIT.Primitive.Inline
-- import Language.HERMIT.Primitive.Debug
import Language.HERMIT.Primitive.Consider -- for cmpName

import qualified Language.Haskell.TH as TH

-- import Debug.Trace
import Control.Monad
import MonadUtils (MonadIO) -- GHC's MonadIO

-- promoteR'  :: Term a => RewriteH a -> RewriteH (Generic a)
-- promoteR' rr = rewrite $ \ c e ->  inject <$> maybe (fail "argument is not an expr") (apply rr c)  (retract e)

externals ::  ExternalReader -> [External]
externals er = map ((.+ Experiment) . (.+ TODO))
         [ external "info" (promoteT info :: TranslateH Core String)
                [ "tell me what you know about this expression or binding" ] .+ Unimplemented
         , external "expr-type" (promoteT exprTypeQueryT :: TranslateH Core String)
                [ "List the type (Constructor) for this expression."]
         , external "test" (testQuery :: RewriteH Core -> TranslateH Core String)
                [ "determines if a rewrite could be successfully applied" ]
         , external "fix-intro" (promoteR fixIntro :: RewriteH Core)
                [ "rewrite a recursive binding into a non-recursive binding using fix" ]
         , external "number-binder" (exprNumberBinder :: Int -> RewriteH Core)
                [ "add a number suffix onto a (lambda) binding" ]
         , external "auto-number-binder" (autoRenameBinder :: RewriteH Core)
                [ "automatically add a number suffix onto a (lambda) binding" ]
         , external "cleanup-unfold" (promoteR cleanupUnfold :: RewriteH Core)
                [ "clean up immeduate nested fully-applied lambdas, from the bottom up"]
         , external "unfold" (promoteR . unfold :: TH.Name -> RewriteH Core)
                [ "inline a definition, and apply the arguments; tranditional unfold"]
         , external "unshadow" (unshadow :: RewriteH Core)
                [ "Rename local variable with manifestly unique names (x, x0, x1, ...)"]
         , external "push" (promoteR . push :: TH.Name -> RewriteH Core)
                [ "push a function <v> into argument" ]
                        -- TODO: does not work with rules with no arguments
         , external "unfold-rule" ((\ nm -> promoteR (rules (er_rules er) nm >>> cleanupUnfold)) :: String -> RewriteH Core)
                [ "apply a named GHC rule" ]
         , external "var" (promoteR . var :: TH.Name -> RewriteH Core)
                [ "var '<v> succeeded for variable v, and fails otherwise"] .+ Predicate
         , external "case-split" (promoteR . caseSplit :: TH.Name -> RewriteH Core)
                [ "case split" ]
         ] ++
         [ external "any-call" (withUnfold :: RewriteH Core -> RewriteH Core)
                [ "any-call (.. unfold command ..) applies an unfold commands to all applications"
                , "preference is given to applications with applications with more arguments"
                ] .+ Deep
         ]


-- Others
-- let v = E1 in E2 E3 <=> (let v = E1 in E2) E3
-- let v = E1 in E2 E3 <=> E2 (let v = E1 in E3)

-- A few Queries.

-- info currently outputs the type of the current CoreExpr
-- TODO: we need something for bindings, etc.
info :: TranslateH CoreExpr String
info = translate $ \ c e ->
          let hd = "Core Expr"
              ty = "type ::= " ++ showSDoc (ppr (exprType e))
              pa = "path :=  " ++ show (contextPath c)
              extra = "extra := " ++ case e of
                                       Var v -> showSDoc (ppIdInfo v (idInfo v))
                                       _     -> "{}"
           in return (unlines [hd,ty,pa,extra])


exprTypeQueryT :: TranslateH CoreExpr String
exprTypeQueryT = arr $ \ e -> case e of
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

findFn :: (MonadUnique m, MonadIO m) => ModGuts -> String -> m Id
findFn modguts nm = do
    namedFn <- case findNameFromTH (mg_rdr_env modguts) $ TH.mkName nm of
        [f] -> return f
        [] -> fail $ "cannot find " ++ nm
        _  -> fail $ "too many " ++ nm ++ " found"

    liftIO $ print ("VAR", GHC.showSDoc . GHC.ppr $ namedFn)

    uq <- getUniqueM
    let n_tyvar = GHC.setTyVarUnique (head alphaTyVars) uq
        n_ty = GHC.mkTyVarTy n_tyvar
        ty = mkForAllTy n_tyvar $ mkFunTy (mkFunTy n_ty n_ty) n_ty
        namedId = GHC.mkVanillaGlobal namedFn ty
        --                mkGlobalVar :: IdDetails -> Name -> Type -> IdInfo -> Id
    return namedId

fixIntro :: RewriteH CoreBind
fixIntro = translate $ \ c e -> case e of
        Rec [(f,e0)] -> do
                fixId <- findFn (hermitModGuts c) "Data.Function.fix"

                let coreFix = App (App (Var fixId) (Type (idType f)))
--                let coreFix = App (Lit (mkMachString "<<FIX>>"))

                -- let rec f = e => let f = fix (\ f -> e)
                -- TODO: check f is not a top-level value
                return $ NonRec f (coreFix (Lam f e0))
        Rec {}       -> fail "recusive group not suitable"
        NonRec {}    -> fail "Cannot take fix of a non-recusive group"


-- ^ Case split a free variable in an expression:
--
-- Assume expression e which mentions x :: [a]
--
-- e ==> case x of x
--         [] -> e
--         (a:b) -> e
caseSplit :: TH.Name -> RewriteH CoreExpr
caseSplit nm = do
    frees <- freeIdsT
    contextfreeT $ \ e -> do
        case [ i | i <- frees, cmpTHName2Name nm (idName i) ] of
            []    -> fail "caseSplit: provided name is not free"
            (i:_) -> do
                let (tycon, tys) = splitTyConApp (idType i)
                    dcs = tyConDataCons tycon
                    aNms = map (:[]) $ cycle ['a'..'z']
                dcsAndVars <- mapM (\dc -> do
                                        as <- sequence [ newVarH (TH.mkName a) ty | (a,ty) <- zip aNms $ dataConInstArgTys dc tys ]
                                        return (dc,as)) dcs
                return $ Case (Var i) i (exprType e) [ (DataAlt dc, as, e) | (dc,as) <- dcsAndVars ]

{-
exprBinder :: TranslateH CoreExpr [(Id,ContextPath)]
exprBinder = translate $ \ c e -> case e of
        Lam b _            -> return [(b,hermitBindingPath c)]
        Let (NonRec b _) _ -> return [(b,hermitBindingPath c)]
        Let (Rec bds) _    -> return [(b,hermitBindingPath c) | b <- map fst bds ]
        _                  -> return []
-}

exprNumberBinder :: Int -> RewriteH Core
exprNumberBinder n = promoteR (exprRenameBinder (++ show n))
                 >>> (childR 0 $ promoteR letSubstR)

exprRenameBinder :: (String -> String) -> RewriteH CoreExpr
exprRenameBinder nameMod =
--            (do observeR "exprRenameBinder" >>> fail "observe") <+
            (do Lam b e <- idR
                (b',f) <- constT (cloneIdH nameMod b)
                return $ Lam b' (f e))
         <+ (do Let (NonRec b e0) e1 <- idR
                (b',f) <- constT (cloneIdH nameMod b)
--                traceR $ "new name = " ++ show (nameMod $ getOccString b')
                return $ Let (NonRec b' e0) (f e1))

altRenameBinder :: (String -> String) -> RewriteH CoreAlt
altRenameBinder nameMod =
             do (con,bs,e) <- idR
                (bs',f) <- constT (cloneIdsH nameMod bs)
                return $ (con,bs',f e)

-- This gives an new version of an Id, with the same info, and a new textual name.
cloneIdH :: (String -> String) -> Id -> HermitM (Id,CoreExpr -> CoreExpr)
cloneIdH nameMod b = do
        uq <- getUniqueM
        let name = mkSystemVarName uq $ mkFastString $ nameMod $ getOccString b
            ty   = idType b
            b'   = mkLocalId name ty
        return (b', Let (NonRec b (Var b')))

cloneIdsH :: (String -> String) -> [Id] -> HermitM ([Id],CoreExpr -> CoreExpr)
cloneIdsH _       []     = return ([],id)
cloneIdsH nameMod (b:bs) = do
        (b',f)   <- cloneIdH  nameMod b
        (bs',fs) <- cloneIdsH nameMod bs
        return (b':bs',f . fs)


-- Here, success is the successful renaming, but if 'id' works, thats okay.
-- AJG: Gut feel, something not quite right here
-- Fails for non-lambdas.

autoRenameBinder :: RewriteH Core
autoRenameBinder =
        promoteR exprAutoRenameBinder
     <+ promoteR altAutoRenameBinder

exprAutoRenameBinder :: RewriteH CoreExpr
exprAutoRenameBinder =
    (do -- check if lambda
        Lam b _ <- idR
        frees <- childT 0 (promoteT freeVarsT) :: TranslateH CoreExpr [Var]
        bound <- translate $ \ c _ -> return (listBindings c)
        exprRenameBinder (inventNames (filter (/= b) (frees ++ bound))) >>> (childR 0 $ promoteR letSubstR))
 <+ (do -- check in Let
        Let (NonRec b _) _ <- idR
        frees <- freeVarsT :: TranslateH CoreExpr [Var]
        bound <- translate $ \ c _ -> return (listBindings c)
        exprRenameBinder (inventNames (filter (/= b) (frees ++ bound))) >>> (childR 0 $ promoteR letSubstR))

altAutoRenameBinder :: RewriteH CoreAlt
altAutoRenameBinder = do
        -- check if alt
        (_,bs,_) <- idR
        frees <- childT 0 (promoteT freeVarsT) :: TranslateH CoreAlt [Var]
        bound <- translate $ \ c _ -> return (listBindings c)
        altRenameBinder (inventNames (filter (\ i -> not (i `elem` bs)) (frees ++ bound))) >>> (childR 1 $ letSubstNR (length bs))

-- remove N lets, please
letSubstNR :: Int -> RewriteH Core
letSubstNR 0 = idR
letSubstNR n = (childR 1 $ letSubstNR (n - 1)) >>> promoteR letSubstR

inventNames :: [Id] -> String -> String
inventNames curr old | trace (show ("inventNames",names,old)) False = undefined
   where
           names = map getOccString curr
inventNames curr old = head
                     [ nm
                     | nm <- old : [ old ++ show uq | uq <- [0..] :: [Int] ]
                     , nm `notElem` names
                     ]
   where
           names = map getOccString curr




-- | cleanupUnfold cleans a unfold operation
--  (for example, an inline or rule application)
-- It is used at the level of the top-redex.
cleanupUnfold :: RewriteH CoreExpr
cleanupUnfold = betaReducePlus >>> safeLetSubstPlusR

unfold :: TH.Name -> RewriteH CoreExpr
unfold nm = translate $ \ env e0 -> do
        let n = countArguments e0
        let sub :: RewriteH Core
            sub = pathR (take n (repeat 0))
                        (promoteR (inlineName nm))

            sub2 :: RewriteH CoreExpr
            sub2 = extractR sub

        e1 <- apply sub2 env e0

        -- only cleanup if 1 or more arguments
        if n > 0 then apply cleanupUnfold env e1
                 else return e1

-- match in a top-down manner,
withUnfold :: RewriteH Core -> RewriteH Core
withUnfold rr = readerT $ \ e -> case e of
        ExprCore (App {}) -> childR 1 rec >+> (rr <+ childR 0 rec)
        ExprCore (Var {}) -> rr
        _                 -> anyR rec
   where

        rec :: RewriteH Core
        rec = withUnfold rr

-- Makes every 'virtual' shadow dispear.
-- O(n^2) right now
-- Also, only does lambda bound things.
unshadow :: RewriteH Core
unshadow = anytdR (promoteR autoRenameBinder)

--cleanUnfold :: (LensH Core Core -> RewriteH Core) -> RewriteH Core
--cleanUnfold f =

countArguments :: CoreExpr -> Int
countArguments (App e1 _) = countArguments e1 + 1
countArguments _          = 0

-- push a variable into the expression
push :: TH.Name -> RewriteH CoreExpr
push nm = do
        e <- idR
        case collectArgs e of
          (Var v,args) -> do
                  when (not (nm `cmpName` idName v)) $ do
                          fail $ "push did not find name " ++ show nm
                  when (length args == 0) $ do
                          fail $ "no argument for " ++ show nm
                  when (not (all isTypeArg (init args))) $ do
                          fail $ " initial arguments are not type arguments for " ++ show nm
                  case last args of
                     Case {} -> caseFloatArg
                     _       -> fail "can not push, sorry"
          _ -> fail "no function to match for push"
