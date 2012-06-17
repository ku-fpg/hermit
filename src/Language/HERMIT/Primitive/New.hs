{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins as GHC hiding (varName)
--import Convert (thRdrNameGuesses)
-- import OccName(varName)

import Control.Applicative
import Control.Arrow

import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitKure
import Language.HERMIT.External
import Language.HERMIT.GHC
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Local

import qualified Language.Haskell.TH as TH


-- promoteR'  :: Term a => RewriteH a -> RewriteH (Generic a)
-- promoteR' rr = rewrite $ \ c e ->  inject <$> maybe (fail "argument is not an expr") (apply rr c)  (retract e)

externals :: [External]
externals = map (.+ Experiment)
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
         , external "cleanup-unfold" (promoteR cleanupUnfold :: RewriteH Core)
                [ "clean up immeduate nested fully-applied lambdas, from the bottom up"]

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

fixIntro :: RewriteH CoreBind
fixIntro = translate $ \ c e -> case e of
        Rec [(f,e0)] -> do
                let modGuts = hermitModGuts c
                let rdrEnv = mg_rdr_env modGuts

                fixVar <- case findNameFromTH rdrEnv $  TH.mkName "Data.Function.fix" of
                             [f'] -> return f'
                             [] -> fail "can not find fix"
                             _  -> fail "to many fix's"

                liftIO $ print ("VAR",GHC.showSDoc . GHC.ppr $ fixVar)

                uq <- getUniqueM
                let n_tyvar = GHC.setTyVarUnique (head alphaTyVars) uq
                let n_ty = GHC.mkTyVarTy n_tyvar

                let fixType = mkForAllTy n_tyvar $ mkFunTy (mkFunTy n_ty n_ty) n_ty
                let fixId = GHC.mkVanillaGlobal fixVar fixType
--                mkGlobalVar :: IdDetails -> Name -> Type -> IdInfo -> Id

                let coreFix = App (App (Var fixId) (Type (idType f)))
--                let coreFix = App (Lit (mkMachString "<<FIX>>"))

                -- let rec f = e => let f = fix (\ f -> e)
                -- TODO: check f is not a top-level value
                return $ NonRec f (coreFix (Lam f e0))
        Rec {}       -> fail "recusive group not suitable"
        NonRec {}    -> fail "Cannot take fix of a non-recusive group"


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
             do Lam b e <- idR
                uq      <- constT getUniqueM
                let name = mkSystemVarName uq $ mkFastString $ nameMod $ getOccString b
                    ty   = idType b
                    b'   = mkLocalId name ty
                return $ Lam b' (Let (NonRec b (Var b')) e)

-- | cleanupUnfold cleans a unfold operation
--  (for example, an inline or rule application)
-- It is used at the level of the top-redex.
cleanupUnfold :: RewriteH CoreExpr
cleanupUnfold = contextfreeT (\ e -> case e of
            -- Spot the lambda
                Lam {}  -> return e
                _       -> fail "no lambda")
         <+ (acceptR (\ e -> case e of
                App {} -> True
                _      -> False) >>>
             focusR (childL 0) (promoteR cleanupUnfold) >>>
             beta_reduce >>>
             tryR safeLetSubstR)


--cleanUnfold :: (LensH Core Core -> RewriteH Core) -> RewriteH Core
--cleanUnfold f =

{-
countArguments :: CoreExpr -> Int
countArguments (App e1 _) = countArguments e1 + 1
countArguments _          = 0
-}

