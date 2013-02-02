module Language.HERMIT.Primitive.FixPoint where

import GhcPlugins as GHC hiding (varName)

import Control.Applicative
import Control.Arrow

import Language.HERMIT.Core
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Local
import Language.HERMIT.Primitive.AlphaConversion
import Language.HERMIT.Primitive.New -- TODO: Sort out heirarchy

import qualified Language.Haskell.TH as TH


externals ::  [External]
externals = map ((.+ Experiment) . (.+ TODO))
         [ external "fix-intro" (promoteDefR fixIntro :: RewriteH Core)
                [ "rewrite a recursive binding into a non-recursive binding using fix" ]
         , external "fix-spec" (promoteExprR fixSpecialization :: RewriteH Core)
                [ "specialize a fix with a given argument"] .+ Shallow
         , external "ww-factorisation" ((\ wrap unwrap -> promoteExprR $ workerWrapperFac wrap unwrap) :: CoreString -> CoreString -> RewriteH Core)
                [ "Worker/Wrapper Factorisation",
                  "For any \"f :: a -> a\", and given \"wrap :: b -> a\" and \"unwrap :: a -> b\" as arguments, then",
                  "fix f  ==>  wrap (fix (unwrap . f . wrap))",
                  "Note: the pre-condition \"fix (wrap . unwrap . f) == fix f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-split" ((\ wrap unwrap -> promoteDefR $ workerWrapperSplit wrap unwrap) :: CoreString -> CoreString -> RewriteH Core)
                [ "Worker/Wrapper Split",
                  "For any \"g :: a\", and given \"wrap :: b -> a\" and \"unwrap :: a -> b\" as arguments, then",
                  "g = expr  ==> g = let f = \\ g -> expr",
                  "                   in let work = unwrap (f (wrap work))",
                  "                       in wrap work",
                  "Note: the pre-condition \"fix (wrap . unwrap . f) == fix f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-assumption-A" ((\ wrap unwrap -> promoteExprR $ wwAssA wrap unwrap) :: CoreString -> CoreString -> RewriteH Core)
                [ "Worker/Wrapper Assumption A",
                  "For a \"wrap :: b -> a\" and an \"unwrap :: b -> a\", then",
                  "wrap (unwrap x)  ==>  x",
                  "Note: only use this if it's true!"
                ] .+ PreCondition
         , external "ww-assumption-B" ((\ wrap unwrap f -> promoteExprR $ wwAssB wrap unwrap f) :: CoreString -> CoreString -> CoreString -> RewriteH Core)
                [ "Worker/Wrapper Assumption B",
                  "For a \"wrap :: b -> a\", an \"unwrap :: b -> a\", and an \"f :: a -> a\" then",
                  "wrap (unwrap (f x))  ==>  f x",
                  "Note: only use this if it's true!"
                ] .+ PreCondition
         , external "ww-assumption-C" ((\ wrap unwrap f -> promoteExprR $ wwAssC wrap unwrap f) :: CoreString -> CoreString -> CoreString -> RewriteH Core)
                [ "Worker/Wrapper Assumption C",
                  "For a \"wrap :: b -> a\", an \"unwrap :: b -> a\", and an \"f :: a -> a\" then",
                  "fix t (\\ x -> wrap (unwrap (f x)))  ==>  fix t f",
                  "Note: only use this if it's true!"
                ] .+ PreCondition
         ]

fixLocation :: String
fixLocation = "Data.Function.fix"

findFixId :: TranslateH a Id
findFixId = findIdT (TH.mkName fixLocation)

guardIsFixId :: Id -> TranslateH a ()
guardIsFixId v = do fixId <- findFixId
                    guardMsg (v == fixId) (var2String v ++ " does not match " ++ fixLocation)


-- |  f = e   ==>   f = fix (\ f -> e)
fixIntro :: RewriteH CoreDef
fixIntro = prefixFailMsg "Fix introduction failed: " $
           do Def f e <- idR
              fixId   <- findFixId
              constT $ do f' <- cloneVarH id f
                          let coreFix  = App (App (Var fixId) (Type (idType f)))
                              emptySub = mkEmptySubst (mkInScopeSet (exprFreeVars e))
                              sub      = extendSubst emptySub f (Var f')
                          return $ Def f (coreFix (Lam f' (substExpr (text "fixIntro") sub e)))

-- ironically, this is an instance of worker/wrapper itself.

fixSpecialization :: RewriteH CoreExpr
fixSpecialization = do

        -- fix (t::*) (f :: t -> t) (a :: t) :: t
        App (App (App (Var fixId) (Type _)) _) _ <- idR

        guardIsFixId fixId

        let r :: RewriteH CoreExpr
            r = multiEtaExpand [TH.mkName "f",TH.mkName "a"]

            sub :: RewriteH Core
            sub = pathR [0,1] (promoteR r)

        App (App (App (Var fx) (Type t))
                 (Lam _ (Lam v2 (App (App e _) _a2)))
            )
            (Type t2) <- extractR sub -- In normal form now

        constT $ do let t' = applyTy t t2

                    v3 <- newIdH "f" t'
                    v4 <- newTyVarH "a" (tyVarKind v2)

                    -- f' :: \/ a -> T [a] -> (\/ b . T [b])
                    let f' = Lam v4 (Cast (Var v3) (mkUnsafeCo t' (applyTy t (mkTyVarTy v4))))
                        e' = Lam v3 (App (App e f') (Type t2))

                    return $ App (App (Var fx) (Type t')) e'


--------------------------------------------------------------------------------------------------

workerWrapperFac :: CoreString -> CoreString -> RewriteH CoreExpr
workerWrapperFac wrapS unwrapS = do wrapE   <- setCoreExprT wrapS
                                    unwrapE <- setCoreExprT unwrapS
                                    monomorphicWorkerWrapperFac wrapE unwrapE

workerWrapperSplit :: CoreString -> CoreString -> RewriteH CoreDef
workerWrapperSplit wrapS unwrapS = do wrapE   <- setCoreExprT wrapS
                                      unwrapE <- setCoreExprT unwrapS
                                      monomorphicWorkerWrapperSplit wrapE unwrapE

-- f      :: a -> a
-- wrap   :: forall x,y..z. b -> a
-- unwrap :: forall p,q..r. a -> b
-- fix tyA f ==> wrap (fix tyB (\ x -> unwrap (f (wrap (Var x)))))
-- Assumes the arguments are monomorphic functions (all type variables have already been applied)
monomorphicWorkerWrapperFac :: CoreExpr -> CoreExpr -> RewriteH CoreExpr
monomorphicWorkerWrapperFac wrap unwrap =
  prefixFailMsg "Worker/wrapper Factorisation failed: " $
  do (tA,f)    <- checkIsFixExpr
     (tyA,tyB) <- checkWrapUnwrapTypes wrap unwrap
     guardMsg (eqType tyA tA) ("wrapper/unwrapper types do not match expression type.")
     x         <- constT (newIdH "x" tyB)
     fixId     <- findFixId
     return $ App wrap
                  (App (App (Var fixId) (Type tyB))
                       (Lam x (App unwrap
                                   (App f
                                        (App wrap
                                             (Var x)
                                        )
                                   )
                              )
                       )
                  )


monomorphicWorkerWrapperSplit :: CoreExpr -> CoreExpr -> RewriteH CoreDef
monomorphicWorkerWrapperSplit wrap unwrap =
  let f    = TH.mkName "f"
      w    = TH.mkName "w"
      work = TH.mkName "work"
      fx   = TH.mkName "fix"
   in
      fixIntro >>> defR ( appAllR idR (letIntro f)
                            >>> letFloatArg
                            >>> letAllR idR ( monomorphicWorkerWrapperFac wrap unwrap
                                                >>> appAllR idR (letIntro w)
                                                >>> letFloatArg
                                                >>> letNonRecAllR (unfold fx >>> alphaLetWith [work] >>> extractR simplifyR) idR
                                                >>> letSubstR
                                                >>> letFloatArg
                                            )
                        )

-- | wrap (unwrap x)  ==>  x
wwAssA :: CoreString -> CoreString -> RewriteH CoreExpr
wwAssA wrapS unwrapS = do App wrap (App unwrap x) <- idR
                          guardMsgM (equalsCoreStringExpr wrapS wrap)     "given wrapper does not match expression."
                          guardMsgM (equalsCoreStringExpr unwrapS unwrap) "given unwrapper does not match expression."
                          _ <- checkWrapUnwrapTypes wrap unwrap
                          return x

-- | wrap (unwrap (f x))  ==>  f x
wwAssB :: CoreString -> CoreString -> CoreString -> RewriteH CoreExpr
wwAssB wrapS unwrapS fS = do App _ (App _ (App f _)) <- idR
                             guardMsgM (equalsCoreStringExpr fS f) "given body function does not match expression."
                             _ <- checkEndoFunction f
                             wwAssA wrapS unwrapS

-- | fix t (\ x -> wrap (unwrap (f x)))  ==>  fix t f
wwAssC :: CoreString -> CoreString -> CoreString -> RewriteH CoreExpr
wwAssC wrapS unwrapS fS = do _ <- checkIsFixExpr
                             appAllR idR (lamR (wwAssB wrapS unwrapS fS) >>> etaReduce)

--------------------------------------------------------------------------------------------------

equalsCoreStringExpr :: CoreString -> CoreExpr -> TranslateH a Bool
equalsCoreStringExpr s e = exprEqual e <$> setCoreExprT s

-- | Check that the expression has the form "fix t (f :: t -> t)", returning "t" and "f".
checkIsFixExpr :: TranslateH CoreExpr (Type,CoreExpr)
checkIsFixExpr = withPatFailMsg (wrongExprForm "fix t f") $ -- fix :: forall a. (a -> a) -> a
                 do App (App (Var fixId) (Type ty)) f <- idR
                    guardIsFixId fixId
                    return (ty,f)

checkEndoFunction :: MonadCatch m => CoreExpr -> m Type
checkEndoFunction f = do (ty1,ty2) <- safeSplitFunTy (exprType f) "endo function"
                         guardMsg (eqType ty1 ty2) ("argument and result types differ.")
                         return ty1

checkWrapUnwrapTypes :: MonadCatch m => CoreExpr -> CoreExpr -> m (Type,Type)
checkWrapUnwrapTypes wrap unwrap = do (wrapTyB,wrapTyA)     <- safeSplitFunTy (exprType wrap) "wrapper"
                                      (unwrapTyA,unwrapTyB) <- safeSplitFunTy (exprType unwrap) "unwrapper"
                                      guardMsg (eqType wrapTyA unwrapTyA) ("argument type of unwrapper does not match result type of wrapper.")
                                      guardMsg (eqType unwrapTyB wrapTyB) ("argument type of wrapper does not match result type of unwrapper.")
                                      return (wrapTyA,wrapTyB)

safeSplitFunTy :: MonadCatch m => Type -> String -> m (Type,Type)
safeSplitFunTy t s = maybe (fail $ "type of " ++ s ++ " is not a function type.") return (splitFunTy_maybe t)

--------------------------------------------------------------------------------------------------
