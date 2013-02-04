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
externals = map (.+ Experiment)
         [ external "fix-intro" (promoteDefR fixIntro :: RewriteH Core)
                [ "rewrite a recursive binding into a non-recursive binding using fix" ]
         -- , external "fix-spec" (promoteExprR fixSpecialization :: RewriteH Core)
         --        [ "specialize a fix with a given argument"] .+ Shallow
         , external "ww-factorisation" ((\ wrap unwrap -> promoteExprBiR $ workerWrapperFac wrap unwrap) :: CoreString -> CoreString -> BiRewriteH Core)
                [ "Worker/Wrapper Factorisation",
                  "For any \"f :: a -> a\", and given \"wrap :: b -> a\" and \"unwrap :: a -> b\" as arguments, then",
                  "fix tyA f  <==>  wrap (fix tyB (\\ b -> unwrap (f (wrap b))))",
                  "Note: the pre-condition \"fix tyA (\\ a -> wrap (unwrap (f a))) == fix tyA f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-fusion" ((\ wrap unwrap work -> promoteExprBiR $ workerWrapperFusion wrap unwrap work) :: CoreString -> CoreString -> CoreString -> BiRewriteH Core)
                [ "Worker/Wrapper Fusion",
                  "Given \"wrap :: b -> a\", \"unwrap :: a -> b\" and \"work :: b\" as arguments, then",
                  "unwrap (wrap work)  <==>  work",
                  "Note: the pre-conditions \"fix tyA (\\ a -> wrap (unwrap (f a))) == fix tyA f\"",
                  "                     and \"work == fix (\\ b -> unwrap (f (wrap)))\" are expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-split" ((\ wrap unwrap -> promoteDefR $ workerWrapperSplit wrap unwrap) :: CoreString -> CoreString -> RewriteH Core)
                [ "Worker/Wrapper Split",
                  "For any \"g :: a\", and given \"wrap :: b -> a\" and \"unwrap :: a -> b\" as arguments, then",
                  "g = expr  ==>  g = let f = \\ g -> expr",
                  "                    in let work = unwrap (f (wrap work))",
                  "                        in wrap work",
                  "Note: the pre-condition \"fix a (wrap . unwrap . f) == fix a f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-assumption-A" ((\ wrap unwrap -> promoteExprBiR $ wwAssA wrap unwrap) :: CoreString -> CoreString -> BiRewriteH Core)
                [ "Worker/Wrapper Assumption A",
                  "For a \"wrap :: b -> a\" and an \"unwrap :: b -> a\", then",
                  "wrap (unwrap x)  <==>  x",
                  "Note: only use this if it's true!"
                ] .+ PreCondition
         , external "ww-assumption-B" ((\ wrap unwrap f -> promoteExprBiR $ wwAssB wrap unwrap f) :: CoreString -> CoreString -> CoreString -> BiRewriteH Core)
                [ "Worker/Wrapper Assumption B",
                  "For a \"wrap :: b -> a\", an \"unwrap :: b -> a\", and an \"f :: a -> a\" then",
                  "wrap (unwrap (f x))  <==>  f x",
                  "Note: only use this if it's true!"
                ] .+ PreCondition
         , external "ww-assumption-C" ((\ wrap unwrap f -> promoteExprBiR $ wwAssC wrap unwrap f) :: CoreString -> CoreString -> CoreString -> BiRewriteH Core)
                [ "Worker/Wrapper Assumption C",
                  "For a \"wrap :: b -> a\", an \"unwrap :: b -> a\", and an \"f :: a -> a\" then",
                  "fix t (\\ x -> wrap (unwrap (f x)))  <==>  fix t f",
                  "Note: only use this if it's true!"
                ] .+ PreCondition
         , external "fix-computation" ((promoteExprBiR fixComputationRule) :: BiRewriteH Core)
                [ "Fixed-Point Computation Rule",
                  "fix t f  <==>  f (fix t f)"
                ]
         , external "rolling-rule" ((promoteExprBiR rollingRule) :: BiRewriteH Core)
                [ "Rolling Rule",
                  "fix tyA (\\ a -> f (g a))  <==>  f (fix tyB (\\ b -> g (f b))"
                ]
         ]

--------------------------------------------------------------------------------------------------

-- |  f = e   ==>   f = fix (\ f -> e)
fixIntro :: RewriteH CoreDef
fixIntro = prefixFailMsg "Fix introduction failed: " $
           do Def f e <- idR
              f' <- constT $ cloneVarH id f
              let emptySub = mkEmptySubst (mkInScopeSet $ exprFreeVars e)
                  sub      = extendSubst emptySub f (Var f')
                  e'       = substExpr (text "fixIntro") sub e
              Def f <$> mkFix (Lam f' e')

--------------------------------------------------------------------------------------------------

-- ironically, this is an instance of worker/wrapper itself.

-- fixSpecialization :: RewriteH CoreExpr
-- fixSpecialization = do

--         -- fix (t::*) (f :: t -> t) (a :: t) :: t
--         App (App (App (Var fixId) (Type _)) _) _ <- idR

--         guardIsFixId fixId

--         let r :: RewriteH CoreExpr
--             r = multiEtaExpand [TH.mkName "f",TH.mkName "a"]

--             sub :: RewriteH Core
--             sub = pathR [0,1] (promoteR r)

--         App (App (App (Var fx) (Type t))
--                  (Lam _ (Lam v2 (App (App e _) _a2)))
--             )
--             (Type t2) <- extractR sub -- In normal form now

--         constT $ do let t' = applyTy t t2

--                     v3 <- newIdH "f" t'
--                     v4 <- newTyVarH "a" (tyVarKind v2)

--                     -- f' :: \/ a -> T [a] -> (\/ b . T [b])
--                     let f' = Lam v4 (Cast (Var v3) (mkUnsafeCo t' (applyTy t (mkTyVarTy v4))))
--                         e' = Lam v3 (App (App e f') (Type t2))

--                     return $ App (App (Var fx) (Type t')) e'


--------------------------------------------------------------------------------------------------

-- | For any "f :: a -> a", and given "wrap :: b -> a" and "unwrap :: a -> b" as arguments, then
--   fix tyA f  <==>  wrap (fix tyB (\\ b -> unwrap (f (wrap b))))
workerWrapperFac :: CoreString -> CoreString -> BiRewriteH CoreExpr
workerWrapperFac wrapS unwrapS = bidirectional wwL wwR
  where
    wwL :: RewriteH CoreExpr
    wwL = prefixFailMsg "worker/wrapper factorisation failed: " $
          do (tyA,tyB,wrap,unwrap) <- parseWrapUnwrap wrapS unwrapS
             (tA,f) <- checkFixExpr
             guardMsg (eqType tyA tA) ("wrapper/unwrapper types do not match fix body type.")
             b  <- constT (newIdH "x" tyB)
             fx <- mkFix (Lam b (App unwrap (App f (App wrap (Var b)))))
             return $ App wrap fx

    wwR :: RewriteH CoreExpr
    wwR = prefixFailMsg "(reverse) worker/wrapper factorisation failed: " $
          withPatFailMsg "not an application" $
          do App wrap fx <- idR
             withPatFailMsg wrongFixBody $
               do (tyB, Lam b (App unwrap (App f (App wrap' (Var b'))))) <- checkFixExpr <<< constant fx
                  guardMsg (b == b') wrongFixBody
                  (_,tyB') <- parseWrapUnwrapMatching wrapS unwrapS wrap unwrap
                  guardMsg (exprEqual wrap wrap') "wrapper does not match applied function"
                  guardMsg (eqType tyB tyB') "Type mismatch: this shouldn't have happened, report this as a bug."
                  mkFix f

    wrongFixBody :: String
    wrongFixBody = "body of fix does not have the form Lam b (App unwrap (App f (App wrap (Var b))))"


-- | Given "wrap :: b -> a", "unwrap :: a -> b" and "work :: b" as arguments, then
--   unwrap (wrap work)  <==>  work
workerWrapperFusion :: CoreString -> CoreString -> CoreString -> BiRewriteH CoreExpr
workerWrapperFusion wrapS unwrapS workS = bidirectional fusL fusR
  where
    fusL :: RewriteH CoreExpr
    fusL = prefixFailMsg "worker/wrapper fusion failed: " $
           withPatFailMsg "not a function applied to two arguments." $
           do App unwrap (App wrap work) <- idR
              (_,tyB) <- parseWrapUnwrapMatching wrapS unwrapS wrap unwrap
              work' <- setCoreExprT workS
              guardMsg (exprEqual work work') "given worker function does not match expression."
              _ <- checkExprType tyB <<< constant work
              return work

    fusR :: RewriteH CoreExpr
    fusR = prefixFailMsg "(reverse) worker/wrapper fusion failed: " $
           do (_,tyB,wrap,unwrap) <- parseWrapUnwrap wrapS unwrapS
              work  <- checkExprType tyB
              work' <- setCoreExprT workS
              guardMsg (exprEqual work work') "given worker function does not match expression."
              return $ App unwrap (App wrap work)

-- | \ wrap unwrap ->  (g = expr  ==>  g = let f = \\ g -> expr in let work = unwrap (f (wrap work)) in wrap work)
workerWrapperSplit :: CoreString -> CoreString -> RewriteH CoreDef
workerWrapperSplit wrap unwrap =
  let f    = TH.mkName "f"
      w    = TH.mkName "w"
      work = TH.mkName "work"
      fx   = TH.mkName "fix"
   in
      fixIntro >>> defR ( appAllR idR (letIntro f)
                            >>> letFloatArg
                            >>> letAllR idR ( forewardT (workerWrapperFac wrap unwrap)
                                                >>> appAllR idR (letIntro w)
                                                >>> letFloatArg
                                                >>> letNonRecAllR (unfold fx >>> alphaLetWith [work] >>> extractR simplifyR) idR
                                                >>> letSubstR
                                                >>> letFloatArg
                                            )
                        )

-- | wrap (unwrap x)  <==>  x
wwAssA :: CoreString -> CoreString -> BiRewriteH CoreExpr
wwAssA wrapS unwrapS = bidirectional wwAL wwAR
  where
    wwAL :: RewriteH CoreExpr
    wwAL = do App wrap (App unwrap x) <- idR
              _ <- parseWrapUnwrapMatching wrapS unwrapS wrap unwrap
              return x

    wwAR :: RewriteH CoreExpr
    wwAR = do (a,_,wrap,unwrap) <- parseWrapUnwrap wrapS unwrapS
              x <- checkExprType a
              return $ App wrap (App unwrap x)

-- | wrap (unwrap (f x))  <==>  f x
wwAssB :: CoreString -> CoreString -> CoreString -> BiRewriteH CoreExpr
wwAssB wrapS unwrapS fS = bidirectional wwBL wwBR
  where
    wwA :: BiRewriteH CoreExpr
    wwA = wwAssA wrapS unwrapS

    wwBL :: RewriteH CoreExpr
    wwBL = do App _ (App _ (App f _)) <- idR
              _  <- checkEndoFunction f
              f' <- setCoreExprT fS
              guardMsg (exprEqual f f') "given body function does not match expression."
              forewardT wwA

    wwBR :: RewriteH CoreExpr
    wwBR = do App f _ <- idR
              _  <- checkEndoFunction f
              f' <- setCoreExprT fS
              guardMsg (exprEqual f f') "given body function does not match expression."
              backwardT wwA


-- | fix t (\ x -> wrap (unwrap (f x)))  <==>  fix t f
wwAssC :: CoreString -> CoreString -> CoreString -> BiRewriteH CoreExpr
wwAssC wrapS unwrapS fS = bidirectional wwCL wwCR
  where
    wwB :: BiRewriteH CoreExpr
    wwB = wwAssB wrapS unwrapS fS

    wwCL :: RewriteH CoreExpr
    wwCL = do _ <- checkFixExpr
              appAllR idR (lamR (forewardT wwB) >>> etaReduce)

    wwCR :: RewriteH CoreExpr
    wwCR = do _ <- checkFixExpr
              appAllR idR (etaExpand (TH.mkName "x") >>> lamR (backwardT wwB))

--------------------------------------------------------------------------------------------------

-- | fix ty f  <==>  f (fix ty f)
fixComputationRule :: BiRewriteH CoreExpr
fixComputationRule = bidirectional computationL computationR
  where
    computationL :: RewriteH CoreExpr
    computationL = prefixFailMsg "fix computation rule failed: " $
                   do (_,f) <- checkFixExpr
                      fixf  <- idR
                      return (App f fixf)

    computationR :: RewriteH CoreExpr
    computationR = prefixFailMsg "fix computation rule failed: " $
                   do App f fixf <- idR
                      (_,f') <- checkFixExpr <<< constant fixf
                      guardMsg (exprEqual f f') "external function does not match internal expression"
                      return fixf


-- | fix tyA (\ a -> f (g a))  <==>  f (fix tyB (\ b -> g (f b))
rollingRule :: BiRewriteH CoreExpr
rollingRule = bidirectional rollingRuleL rollingRuleR
  where
    rollingRuleL :: RewriteH CoreExpr
    rollingRuleL = prefixFailMsg "rolling rule failed: " $
                   withPatFailMsg wrongFixBody $
                   do (tyA, Lam a (App f (App g (Var a')))) <- checkFixExpr
                      guardMsg (a == a') wrongFixBody
                      (tyA',tyB) <- checkFunctionsWithInverseTypes g f
                      guardMsg (eqType tyA tyA') "Type mismatch: this shouldn't have happened, report this as a bug."
                      res <- rollingRuleResult tyB g f
                      return (App f res)

    rollingRuleR :: RewriteH CoreExpr
    rollingRuleR = prefixFailMsg "(reversed) rolling rule failed: " $
                   withPatFailMsg "not an application" $
                   do App f fx <- idR
                      withPatFailMsg wrongFixBody $
                        do (tyB, Lam b (App g (App f' (Var b')))) <- checkFixExpr <<< constant fx
                           guardMsg (b == b') wrongFixBody
                           guardMsg (exprEqual f f') "external function does not match internal expression"
                           (tyA,tyB') <- checkFunctionsWithInverseTypes g f
                           guardMsg (eqType tyB tyB') "Type mismatch: this shouldn't have happened, report this as a bug."
                           rollingRuleResult tyA f g

    rollingRuleResult :: Type -> CoreExpr -> CoreExpr -> TranslateH z CoreExpr
    rollingRuleResult ty f g = do x <- constT (newIdH "x" ty)
                                  mkFix (Lam x (App f (App g (Var x))))

    wrongFixBody :: String
    wrongFixBody = "body of fix does not have the form Lam v (App f (App g (Var v)))"

--------------------------------------------------------------------------------------------------

-- | As 'parseWrapUnwrap' but also checks that the parsed string match the given expressions.
parseWrapUnwrapMatching :: CoreString -> CoreString -> CoreExpr -> CoreExpr -> TranslateH z (Type,Type)
parseWrapUnwrapMatching wrapS unwrapS wrapE unwrapE = do (a,b,wrap,unwrap) <- parseWrapUnwrap wrapS unwrapS
                                                         guardMsg (exprEqual wrap wrapE) "given wrapper does not match expression"
                                                         guardMsg (exprEqual unwrap unwrapE) "given unwrapper does not match expression"
                                                         return (a,b)

-- | Given "wrap" and "unwrap" strings, returns types A and B, and "wrap" and "unwrap" expressions.
parseWrapUnwrap :: CoreString -> CoreString -> TranslateH z (Type,Type,CoreExpr,CoreExpr)
parseWrapUnwrap wrapS unwrapS = do wrap   <- setCoreExprT wrapS
                                   unwrap <- setCoreExprT unwrapS
                                   setFailMsg "given expressions do not form a valid wrap/unwrap pair." $
                                     do (a,b) <- checkFunctionsWithInverseTypes unwrap wrap
                                        return (a,b,wrap,unwrap)

checkExprType :: Type -> RewriteH CoreExpr
checkExprType t = do e <- idR
                     guardMsg (exprType e `eqType` t) "expression has wrong type."
                     return e

-- | Check that the expression has the form "fix t (f :: t -> t)", returning "t" and "f".
checkFixExpr :: TranslateH CoreExpr (Type,CoreExpr)
checkFixExpr = withPatFailMsg (wrongExprForm "fix t f") $ -- fix :: forall a. (a -> a) -> a
               do App (App (Var fixId) (Type ty)) f <- idR
                  guardIsFixId fixId
                  return (ty,f)

checkEndoFunction :: MonadCatch m => CoreExpr -> m Type
checkEndoFunction f = do (ty1,ty2) <- typesOfFunExpr f
                         guardMsg (eqType ty1 ty2) ("argument and result types differ.")
                         return ty1

checkFunctionsWithInverseTypes :: MonadCatch m => CoreExpr -> CoreExpr -> m (Type,Type)
checkFunctionsWithInverseTypes f g = do (fdom,fcod) <- typesOfFunExpr f
                                        (gdom,gcod) <- typesOfFunExpr g
                                        guardMsg (eqType fdom gcod) ("functions do not have inverse types.")
                                        guardMsg (eqType gdom fcod) ("functions do not have inverse types.")
                                        return (fdom,fcod)

typesOfFunExpr :: MonadCatch m => CoreExpr -> m (Type,Type)
typesOfFunExpr e = maybe (fail "not a function type.") return (splitFunTy_maybe $ exprType e)

--------------------------------------------------------------------------------------------------

-- | f -> fix f
mkFix :: CoreExpr -> TranslateH z CoreExpr
mkFix f = do t <- checkEndoFunction f
             fixId <- findFixId
             return $ App (App (Var fixId) (Type t)) f

fixLocation :: String
fixLocation = "Data.Function.fix"

findFixId :: TranslateH a Id
findFixId = findIdT (TH.mkName fixLocation)

guardIsFixId :: Id -> TranslateH a ()
guardIsFixId v = do fixId <- findFixId
                    guardMsg (v == fixId) (var2String v ++ " does not match " ++ fixLocation)

--------------------------------------------------------------------------------------------------
