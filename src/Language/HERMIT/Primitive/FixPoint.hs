module Language.HERMIT.Primitive.FixPoint
       ( -- * Operations on the Fixed Point Operator (fix)
         -- | Note that many of these operations require 'Data.Function.fix' to be in scope.
         Language.HERMIT.Primitive.FixPoint.externals
         -- ** Rewrites and BiRewrites on Fixed Points
       , fixIntro
       , fixComputationRule
       , rollingRule
       )
where

import GhcPlugins as GHC hiding (varName)

import Control.Applicative
import Control.Arrow

import Data.Monoid (mempty)

import Language.HERMIT.Core
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC

import Language.HERMIT.Primitive.AlphaConversion
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.Composite
import Language.HERMIT.Primitive.Function
import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Local
import Language.HERMIT.Primitive.Navigation
import Language.HERMIT.Primitive.New -- TODO: Sort out heirarchy
import Language.HERMIT.Primitive.Unfold

import qualified Language.Haskell.TH as TH

--------------------------------------------------------------------------------------------------

-- | Externals for manipulating fixed points, and for the worker/wrapper transformation.
externals ::  [External]
externals = map (.+ Experiment)
         [ external "fix-intro" (promoteDefR fixIntro :: RewriteH Core)
                [ "rewrite a recursive binding into a non-recursive binding using fix"
                ] .+ Introduce .+ Context
         , external "fix-computation" (promoteExprBiR fixComputationRule :: BiRewriteH Core)
                [ "Fixed-Point Computation Rule",
                  "fix t f  <==>  f (fix t f)"
                ]
         , external "rolling-rule" (promoteExprBiR rollingRule :: BiRewriteH Core)
                [ "Rolling Rule",
                  "fix tyA (\\ a -> f (g a))  <==>  f (fix tyB (\\ b -> g (f b))"
                ]
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
         , external "ww-split-param" ((\ n wrap unwrap -> promoteDefR $ workerWrapperSplitParam n wrap unwrap) :: Int -> CoreString -> CoreString -> RewriteH Core)
                [ "Worker/Wrapper Split - Type Paramater Variant",
                  "For any \"g :: forall t1 t2 .. tn . a\", and given \"wrap :: forall t1 t2 .. tn . b -> a\" and \"unwrap :: forall t1 t2 .. tn . a -> b\" as arguments, then",
                  "g = expr  ==>  g = \\ t1 t2 .. tn -> let f = \\ g -> expr t1 t2 .. tn",
                  "                                      in let work = unwrap t1 t2 .. tn (f (wrap t1 t2  ..tn work))",
                  "                                          in wrap t1 t2 .. tn work"
                ] .+ Introduce .+ Context .+ PreCondition .+ TODO .+ Experiment
         , external "ww-assumption-A" ((\ wrap unwrap -> promoteExprBiR $ wwA wrap unwrap) :: CoreString -> CoreString -> BiRewriteH Core)
                [ "Worker/Wrapper Assumption A",
                  "For a \"wrap :: b -> a\" and an \"unwrap :: b -> a\", then",
                  "wrap (unwrap x)  <==>  x",
                  "Note: only use this if it's true!"
                ] .+ Context .+ PreCondition
         , external "ww-assumption-B" ((\ wrap unwrap f -> promoteExprBiR $ wwB wrap unwrap f) :: CoreString -> CoreString -> CoreString -> BiRewriteH Core)
                [ "Worker/Wrapper Assumption B",
                  "For a \"wrap :: b -> a\", an \"unwrap :: b -> a\", and an \"f :: a -> a\" then",
                  "wrap (unwrap (f x))  <==>  f x",
                  "Note: only use this if it's true!"
                ] .+ Context .+ PreCondition
         , external "ww-assumption-C" ((\ wrap unwrap f -> promoteExprBiR $ wwC wrap unwrap f) :: CoreString -> CoreString -> CoreString -> BiRewriteH Core)
                [ "Worker/Wrapper Assumption C",
                  "For a \"wrap :: b -> a\", an \"unwrap :: b -> a\", and an \"f :: a -> a\" then",
                  "fix t (\\ x -> wrap (unwrap (f x)))  <==>  fix t f",
                  "Note: only use this if it's true!"
                ] .+ Context .+ PreCondition
         ]

--------------------------------------------------------------------------------------------------

-- |  @f = e@   ==\>   @f = fix (\\ f -> e)@
fixIntro :: RewriteH CoreDef
fixIntro = prefixFailMsg "fix introduction failed: " $
           do Def f _ <- idR
              f' <- constT $ cloneVarH id f
              Def f <$> (mkFix =<< (defT mempty (extractR $ substR f $ varToCoreExpr f') (\ () e' -> Lam f' e')))

--------------------------------------------------------------------------------------------------

-- | @fix ty f@  \<==\>  @f (fix ty f)@
fixComputationRule :: BiRewriteH CoreExpr
fixComputationRule = bidirectional computationL computationR
  where
    computationL :: RewriteH CoreExpr
    computationL = prefixFailMsg "fix computation rule failed: " $
                   do (_,f) <- isFixExpr
                      fixf  <- idR
                      return (App f fixf)

    computationR :: RewriteH CoreExpr
    computationR = prefixFailMsg "fix computation rule failed: " $
                   do App f fixf <- idR
                      (_,f') <- isFixExpr <<< constant fixf
                      guardMsg (exprEqual f f') "external function does not match internal expression"
                      return fixf


-- | @fix tyA (\\ a -> f (g a))@  \<==\>  @f (fix tyB (\\ b -> g (f b))@
rollingRule :: BiRewriteH CoreExpr
rollingRule = bidirectional rollingRuleL rollingRuleR
  where
    rollingRuleL :: RewriteH CoreExpr
    rollingRuleL = prefixFailMsg "rolling rule failed: " $
                   withPatFailMsg wrongFixBody $
                   do (tyA, Lam a (App f (App g (Var a')))) <- isFixExpr
                      guardMsg (a == a') wrongFixBody
                      (tyA',tyB) <- funsWithInverseTypes g f
                      guardMsg (eqType tyA tyA') "Type mismatch: this shouldn't have happened, report this as a bug."
                      res <- rollingRuleResult tyB g f
                      return (App f res)

    rollingRuleR :: RewriteH CoreExpr
    rollingRuleR = prefixFailMsg "(reversed) rolling rule failed: " $
                   withPatFailMsg "not an application." $
                   do App f fx <- idR
                      withPatFailMsg wrongFixBody $
                        do (tyB, Lam b (App g (App f' (Var b')))) <- isFixExpr <<< constant fx
                           guardMsg (b == b') wrongFixBody
                           guardMsg (exprEqual f f') "external function does not match internal expression"
                           (tyA,tyB') <- funsWithInverseTypes g f
                           guardMsg (eqType tyB tyB') "Type mismatch: this shouldn't have happened, report this as a bug."
                           rollingRuleResult tyA f g

    rollingRuleResult :: Type -> CoreExpr -> CoreExpr -> TranslateH z CoreExpr
    rollingRuleResult ty f g = do x <- constT (newIdH "x" ty)
                                  mkFix (Lam x (App f (App g (Var x))))

    wrongFixBody :: String
    wrongFixBody = "body of fix does not have the form: Lam v (App f (App g (Var v)))"

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

-- | For any @f :: a -> a@, and given @wrap :: b -> a@ and @unwrap :: a -> b@ as arguments, then
--   @fix tyA f@  \<==\>  @wrap (fix tyB (\\ b -> unwrap (f (wrap b))))@
workerWrapperFacBR :: CoreExpr -> CoreExpr -> BiRewriteH CoreExpr
workerWrapperFacBR wrap unwrap = beforeBiR (wrapUnwrapTypes wrap unwrap)
                                           (\ (tyA,tyB) -> bidirectional (wwL tyA tyB) wwR)
  where
    wwL :: Type -> Type -> RewriteH CoreExpr
    wwL tyA tyB = prefixFailMsg "worker/wrapper factorisation failed: " $
                  do (tA,f)    <- isFixExpr
                     guardMsg (eqType tyA tA) ("wrapper/unwrapper types do not match fix body type.")
                     b  <- constT (newIdH "x" tyB)
                     fx <- mkFix (Lam b (App unwrap (App f (App wrap (Var b)))))
                     return $ App wrap fx

    wwR :: RewriteH CoreExpr
    wwR = prefixFailMsg "(reverse) worker/wrapper factorisation failed: " $
          withPatFailMsg "not an application." $
          do App wrap2 fx <- idR
             withPatFailMsg wrongFixBody $
               do (_, Lam b (App unwrap1 (App f (App wrap1 (Var b'))))) <- isFixExpr <<< constant fx
                  guardMsg (b == b') wrongFixBody
                  guardMsg (exprEqual wrap wrap2) "given wrapper does not match applied function."
                  guardMsg (exprEqual wrap wrap1) "given wrapper does not match wrapper in body of fix."
                  guardMsg (exprEqual unwrap unwrap1) "given unwrapper does not match unwrapper in body of fix."
                  mkFix f

    wrongFixBody :: String
    wrongFixBody = "body of fix does not have the form Lam b (App unwrap (App f (App wrap (Var b))))"

-- | For any @f :: a -> a@, and given @wrap :: b -> a@ and @unwrap :: a -> b@ as arguments, then
--   @fix tyA f@  \<==\>  @wrap (fix tyB (\\ b -> unwrap (f (wrap b))))@
workerWrapperFac :: CoreString -> CoreString -> BiRewriteH CoreExpr
workerWrapperFac = parse2beforeBiR workerWrapperFacBR

--------------------------------------------------------------------------------------------------

-- | Given @wrap :: b -> a@, @unwrap :: a -> b@ and @work :: b@ as arguments, then
--   @unwrap (wrap work)@  \<==\>  @work@
workerWrapperFusionBR :: CoreExpr -> CoreExpr -> CoreExpr -> BiRewriteH CoreExpr
workerWrapperFusionBR wrap unwrap work = beforeBiR (prefixFailMsg "worker/wrapper fusion failed: " $
                                                    do (_,tyB) <- wrapUnwrapTypes wrap unwrap
                                                       guardMsg (exprType work `eqType` tyB) "type of worker does not match types of wrap/unwrap."
                                                   )
                                                   (\ () -> bidirectional fusL fusR)
  where
    fusL :: RewriteH CoreExpr
    fusL = prefixFailMsg "worker/wrapper fusion failed: " $
           withPatFailMsg (wrongExprForm "App unwrap (App wrap work)") $
           do App unwrap' (App wrap' work') <- idR
              guardMsg (exprEqual wrap wrap') "given wrapper does not match wrapper in expression."
              guardMsg (exprEqual unwrap unwrap') "given unwrapper does not match unwrapper in expression."
              guardMsg (exprEqual work work') "given worker function does not worker in expression."
              return work

    fusR :: RewriteH CoreExpr
    fusR = prefixFailMsg "(reverse) worker/wrapper fusion failed: " $
           do work' <- idR
              guardMsg (exprEqual work work') "given worker function does not match expression."
              return $ App unwrap (App wrap work)

-- | Given @wrap :: b -> a@, @unwrap :: a -> b@ and @work :: b@ as arguments, then
--   @unwrap (wrap work)@  \<==\>  @work@
workerWrapperFusion :: CoreString -> CoreString -> CoreString -> BiRewriteH CoreExpr
workerWrapperFusion = parse3beforeBiR workerWrapperFusionBR

--------------------------------------------------------------------------------------------------

-- | \\ wrap unwrap ->  (@g = expr@  ==>  @g = let f = \\ g -> expr in let work = unwrap (f (wrap work)) in wrap work)@
workerWrapperSplitR :: CoreExpr -> CoreExpr -> RewriteH CoreDef
workerWrapperSplitR wrap unwrap =
  let work = TH.mkName "work"
      fx   = TH.mkName "fix"
   in
      fixIntro >>> defAllR idR ( appAllR idR (letIntro "f")
                                  >>> letFloatArg
                                  >>> letAllR idR ( forewardT (workerWrapperFacBR wrap unwrap)
                                                     >>> appAllR idR (letIntro "w")
                                                     >>> letFloatArg
                                                     >>> letNonRecAllR idR (unfoldNameR fx >>> alphaLetWith [work] >>> extractR simplifyR) idR
                                                     >>> letSubstR
                                                     >>> letFloatArg
                                                  )
                               )

-- | \\ wrap unwrap ->  (@g = expr@  ==>  @g = let f = \\ g -> expr in let work = unwrap (f (wrap work)) in wrap work)@
workerWrapperSplit :: CoreString -> CoreString -> RewriteH CoreDef
workerWrapperSplit wrapS unwrapS = (parseCoreExprT wrapS &&& parseCoreExprT unwrapS) >>= uncurry workerWrapperSplitR

-- | As 'workerWrapperSplit' but performs the static-argument transformation for @n@ type paramaters first, providing these types as arguments to all calls of wrap and unwrap.
--   This is useful if the expression, and wrap and unwrap, all have a @forall@ type.
workerWrapperSplitParam :: Int -> CoreString -> CoreString -> RewriteH CoreDef
workerWrapperSplitParam 0 = workerWrapperSplit
workerWrapperSplitParam n = \ wrapS unwrapS -> prefixFailMsg "worker/wrapper split (forall variant) failed: " $
                                               do guardMsg (n == 1) "currently only supports 1 type paramater."
                                                  withPatFailMsg "right-hand-side of definition does not have the form: Lam t e" $
                                                    do Def _ (Lam t _) <- idR
                                                       guardMsg (isTyVar t) "first argument is not a type."
                                                       let splitAtDefR :: RewriteH Core
                                                           splitAtDefR = do p <- considerConstructT Definition
                                                                            localPathR p
                                                                              $ promoteR $ do wrap   <- parseCoreExprT wrapS
                                                                                              unwrap <- parseCoreExprT unwrapS
                                                                                              let ty = Type (TyVarTy t)
                                                                                              workerWrapperSplitR (App wrap ty) (App unwrap ty)
                                                       staticArgR >>> extractR splitAtDefR

--------------------------------------------------------------------------------------------------

-- | @wrap (unwrap x)@  \<==\>  @x@
wwAssA :: CoreExpr -> CoreExpr -> BiRewriteH CoreExpr
wwAssA wrap unwrap = beforeBiR (wrapUnwrapTypes wrap unwrap) (\ (tyA,_) -> bidirectional wwAL (wwAR tyA))
  where
    wwAL :: RewriteH CoreExpr
    wwAL = withPatFailMsg (wrongExprForm "App wrap (App unwrap x)") $
           do App wrap' (App unwrap' x) <- idR
              guardMsg (exprEqual wrap wrap')     "given wrapper does not match wrapper in expression."
              guardMsg (exprEqual unwrap unwrap') "given unwrapper does not match unwrapper in expression."
              return x

    wwAR :: Type -> RewriteH CoreExpr
    wwAR tyA = do x <- idR
                  guardMsg (exprType x `eqType` tyA) "type of expression does not match types of wrap/unwrap."
                  return $ App wrap (App unwrap x)

-- | @wrap (unwrap x)@  \<==\>  @x@
wwA :: CoreString -> CoreString -> BiRewriteH CoreExpr
wwA = parse2beforeBiR wwAssA


-- | @wrap (unwrap (f x))@  \<==\>  @f x@
wwAssB :: CoreExpr -> CoreExpr -> CoreExpr -> BiRewriteH CoreExpr
wwAssB wrap unwrap f = bidirectional wwBL wwBR
  where
    assA :: BiRewriteH CoreExpr
    assA = wwAssA wrap unwrap

    wwBL :: RewriteH CoreExpr
    wwBL = withPatFailMsg (wrongExprForm "App wrap (App unwrap (App f x))") $
           do App _ (App _ (App f' _)) <- idR
              guardMsg (exprEqual f f') "given body function does not match expression."
              forewardT assA

    wwBR :: RewriteH CoreExpr
    wwBR = withPatFailMsg (wrongExprForm "App f x") $
           do App f' _ <- idR
              guardMsg (exprEqual f f') "given body function does not match expression."
              backwardT assA

-- | @wrap (unwrap (f x))@  \<==\>  @f x@
wwB :: CoreString -> CoreString -> CoreString -> BiRewriteH CoreExpr
wwB = parse3beforeBiR wwAssB


-- | @fix t (\ x -> wrap (unwrap (f x)))@  \<==\>  @fix t f@
wwAssC :: CoreExpr -> CoreExpr -> CoreExpr -> BiRewriteH CoreExpr
wwAssC wrap unwrap f = beforeBiR isFixExpr (\ _ -> bidirectional wwCL wwCR)
  where
    assB :: BiRewriteH CoreExpr
    assB = wwAssB wrap unwrap f

    wwCL :: RewriteH CoreExpr
    wwCL = appAllR idR (lamAllR idR (forewardT assB) >>> etaReduce)

    wwCR :: RewriteH CoreExpr
    wwCR = appAllR idR (etaExpand "x" >>> lamAllR idR (backwardT assB))

-- | @fix t (\ x -> wrap (unwrap (f x)))@  \<==\>  @fix t f@
wwC :: CoreString -> CoreString -> CoreString -> BiRewriteH CoreExpr
wwC = parse3beforeBiR wwAssC

--------------------------------------------------------------------------------------------------

-- | Check that the expression has the form "fix t (f :: t -> t)", returning "t" and "f".
isFixExpr :: TranslateH CoreExpr (Type,CoreExpr)
isFixExpr = withPatFailMsg (wrongExprForm "fix t f") $ -- fix :: forall a. (a -> a) -> a
            do App (App (Var fixId) (Type ty)) f <- idR
               fixId' <- findFixId
               guardMsg (fixId == fixId') (var2String fixId ++ " does not match " ++ fixLocation)
               return (ty,f)

wrapUnwrapTypes :: MonadCatch m => CoreExpr -> CoreExpr -> m (Type,Type)
wrapUnwrapTypes wrap unwrap = setFailMsg "given expressions have the wrong types to form a valid wrap/unwrap pair." $
                              funsWithInverseTypes unwrap wrap

--------------------------------------------------------------------------------------------------

-- | f  ==>  fix f
mkFix :: CoreExpr -> TranslateH z CoreExpr
mkFix f = do t <- endoFunType f
             fixId <- findFixId
             return $ mkCoreApps (varToCoreExpr fixId) [Type t, f]

fixLocation :: String
fixLocation = "Data.Function.fix"

findFixId :: TranslateH a Id
findFixId = findIdT (TH.mkName fixLocation)

--------------------------------------------------------------------------------------------------

parse2beforeBiR :: (CoreExpr -> CoreExpr -> BiRewriteH a) -> CoreString -> CoreString -> BiRewriteH a
parse2beforeBiR f s1 s2 = beforeBiR (parseCoreExprT s1 &&& parseCoreExprT s2) (uncurry f)

parse3beforeBiR :: (CoreExpr -> CoreExpr -> CoreExpr -> BiRewriteH a) -> CoreString -> CoreString -> CoreString -> BiRewriteH a
parse3beforeBiR f s1 s2 s3 = beforeBiR ((parseCoreExprT s1 &&& parseCoreExprT s2) &&& parseCoreExprT s3) ((uncurry.uncurry) f)

--------------------------------------------------------------------------------------------------
