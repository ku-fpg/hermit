{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- Placeholder for new prims
module Language.HERMIT.Primitive.New where

import GhcPlugins as GHC hiding (varName)
--import Convert (thRdrNameGuesses)
import OccName(varName)

import Control.Applicative
import Control.Arrow

import Language.KURE
import Language.KURE.Injection

import Language.HERMIT.HermitMonad
import Language.HERMIT.HermitEnv
import Language.HERMIT.HermitKure
import Language.HERMIT.External
import Language.HERMIT.GHC

import qualified Language.Haskell.TH as TH


promoteR'  :: Term a => RewriteH a -> RewriteH (Generic a)
promoteR' rr = rewrite $ \ c e ->  inject <$> maybe (fail "argument is not an expr") (apply rr c)  (retract e)

externals :: [External]
externals = map (.+ Experiment)
         [
           external "let-intro" (promoteR' . let_intro :: TH.Name -> RewriteH Core)
                [ "'let-intro v' performs E1 ==> (let v = E1 in v)" ]
         , external "info" (promoteT info :: TranslateH Core String)
                [ "tell me what you know about this expression or binding" ] .+ Unimplemented
         , external "expr-type" (promoteT exprTypeQueryT :: TranslateH Core String)
                [ "List the type (Constructor) for this expression."]
         , external "test" (testQuery :: RewriteH Core -> TranslateH Core String)
                [ "determines if a rewrite could be successfully applied" ]
         , external "fix-intro" (promoteR fixIntro :: RewriteH Core)
                [ "rewrite a recursive binding into a non-recursive binding using fix" ]
         ]

let_intro ::  TH.Name -> RewriteH CoreExpr
let_intro nm = rewrite $ \ _ e -> do letvar <- newVarH nm (exprType e)
                                     return $ Let (NonRec letvar e) (Var letvar)

-- Others
-- let v = E1 in E2 E3 <=> (let v = E1 in E2) E3
-- let v = E1 in E2 E3 <=> E2 (let v = E1 in E3)

-- A few Queries.

-- info currently outputs the type of the current CoreExpr
-- TODO: we need something for bindings, etc.
info :: TranslateH CoreExpr String
info = do ContextPath this <- pathT
          translate $ \ cxt e -> do
                  let hd = "Core Expr"
                      ty = "type ::= " ++ showSDoc (ppr (exprType e))
                      pa = "path :=  " ++ show (reverse this)
                      extra = "extra := " ++ case e of
                                Var v -> showSDoc (ppIdInfo v (idInfo v))
                                _ -> "{}"
                  return (unlines [hd,ty,pa,extra])


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
                             [f] -> return f
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
        NonRec {}    -> fail "Can not take fix of a non-recusive group"

{-
Main.f :: forall t_a9Y. (t_a9Y -> t_a9Y) -> t_a9Y
[GblId, Arity=1, Caf=NoCafRefs]
Main.f =
  \ (@ t_aa0) (g_a9T :: t_aa0 -> t_aa0) ->
    letrec {
      x_a9V [Occ=LoopBreaker] :: t_aa0
      [LclId]
      x_a9V = g_a9T x_a9V; } in
    x_a9V

-- | Make a 'build' expression applied to a locally-bound worker function
mkBuildExpr :: (MonadThings m, MonadUnique m)
            => Type                                     -- ^ Type of list elements to be built
            -> ((Id, Type) -> (Id, Type) -> m CoreExpr) -- ^ Function that, given information about the 'Id's
                                                        -- of the binders for the build worker function, returns
                                                        -- the body of that worker
            -> m CoreExpr
mkBuildExpr elt_ty mk_build_inside = do
    [n_tyvar] <- newTyVars [alphaTyVar]
    let n_ty = mkTyVarTy n_tyvar
        c_ty = mkFunTys [elt_ty, n_ty] n_ty
    [c, n] <- sequence [mkSysLocalM (fsLit "c") c_ty, mkSysLocalM (fsLit "n") n_ty]

    build_inside <- mk_build_inside (c, c_ty) (n, n_ty)

    build_id <- lookupId buildName
    return $ Var build_id `App` Type elt_ty `App` mkLams [n_tyvar, c, n] build_inside
  where
    newTyVars tyvar_tmpls = do
      uniqs <- getUniquesM
      return (zipWith setTyVarUnique tyvar_tmpls uniqs)
-}

