module HERMIT.Primitive.WorkerWrapper
       ( -- * The Worker/Wrapper Transformation
         -- | Note that many of these operations require 'Data.Function.fix' to be in scope.
         HERMIT.Primitive.WorkerWrapper.externals
       , workerWrapperFacBR
       , workerWrapperFusionBR
       , workerWrapperSplitR
       , workerWrapperSplitParam
       , wwAssA
       , wwAssB
       , wwAssC
       )
where

import GhcPlugins as GHC hiding (varName)

import Control.Applicative
import Control.Arrow

import HERMIT.Core
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC

import HERMIT.Primitive.AlphaConversion
import HERMIT.Primitive.Common
import HERMIT.Primitive.Function
import HERMIT.Primitive.GHC
import HERMIT.Primitive.Local
import HERMIT.Primitive.Navigation
import HERMIT.Primitive.New -- TODO: Sort out heirarchy
import HERMIT.Primitive.FixPoint
import HERMIT.Primitive.Unfold

import qualified Language.Haskell.TH as TH

--------------------------------------------------------------------------------------------------

-- | Externals for manipulating fixed points, and for the worker/wrapper transformation.
externals ::  [External]
externals = map (.+ Experiment)
         [
           external "ww-factorisation" ((\ wrap unwrap assC -> promoteExprBiR $ workerWrapperFac (mkWWAssC assC) wrap unwrap)
                                          :: CoreString -> CoreString -> RewriteH Core -> BiRewriteH Core)
                [ "Worker/Wrapper Factorisation",
                  "For any \"f :: a -> a\", and given \"wrap :: b -> a\" and \"unwrap :: a -> b\" as arguments,",
                  "and a proof of Assumption C (fix tyA (\\ a -> wrap (unwrap (f a))) ==> fix tyA f), then",
                  "fix tyA f  ==>  wrap (fix tyB (\\ b -> unwrap (f (wrap b))))"
                ] .+ Introduce .+ Context
         , external "ww-factorisation-unsafe" ((\ wrap unwrap -> promoteExprBiR $ workerWrapperFac Nothing wrap unwrap)
                                               :: CoreString -> CoreString -> BiRewriteH Core)
                [ "Unsafe Worker/Wrapper Factorisation",
                  "For any \"f :: a -> a\", and given \"wrap :: b -> a\" and \"unwrap :: a -> b\" as arguments, then",
                  "fix tyA f  <==>  wrap (fix tyB (\\ b -> unwrap (f (wrap b))))",
                  "Note: the pre-condition \"fix tyA (\\ a -> wrap (unwrap (f a))) == fix tyA f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-fusion" ((\ wrap unwrap work assC -> promoteExprBiR $ workerWrapperFusion (mkWWAssC assC) wrap unwrap work)
                                 :: CoreString -> CoreString -> CoreString -> RewriteH Core -> BiRewriteH Core)
                [ "Worker/Wrapper Fusion",
                  "Given \"wrap :: b -> a\", \"unwrap :: a -> b\" and \"work :: b\" as arguments,",
                  "and a proof of Assumption C (fix tyA (\\ a -> wrap (unwrap (f a))) ==> fix tyA f), then",
                  "unwrap (wrap work)  <==>  work",
                  "Note: you are required to have previously executed the command \"ww-generate-fusion\" on the definition",
                  "      work == unwrap (f (wrap work))"
                ] .+ Introduce .+ Context .+ PreCondition .+ TODO
         , external "ww-fusion-unsafe" ((\ wrap unwrap work -> promoteExprBiR $ workerWrapperFusion Nothing wrap unwrap work)
                                 :: CoreString -> CoreString -> CoreString -> BiRewriteH Core)
                [ "Unsafe Worker/Wrapper Fusion",
                  "Given \"wrap :: b -> a\", \"unwrap :: a -> b\" and \"work :: b\" as arguments, then",
                  "unwrap (wrap work)  <==>  work",
                  "Note: the pre-conditions \"fix tyA (\\ a -> wrap (unwrap (f a))) == fix tyA f\"",
                  "                     and \"work == fix (\\ b -> unwrap (f (wrap b)))\" are expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-split" ((\ wrap unwrap assC -> promoteDefR $ workerWrapperSplit (mkWWAssC assC) wrap unwrap)
                                  :: CoreString -> CoreString -> RewriteH Core -> RewriteH Core)
                [ "Worker/Wrapper Split",
                  "For any \"prog :: a\", and given \"wrap :: b -> a\" and \"unwrap :: a -> b\" as arguments,",
                  "and a proof of Assumption C (fix tyA (\\ a -> wrap (unwrap (f a))) ==> fix tyA f), then",
                  "prog = expr  ==>  prog = let f = \\ prog -> expr",
                  "                          in let work = unwrap (f (wrap work))",
                  "                              in wrap work"
                ] .+ Introduce .+ Context
         , external "ww-split-unsafe" ((\ wrap unwrap -> promoteDefR $ workerWrapperSplit Nothing wrap unwrap)
                                       :: CoreString -> CoreString -> RewriteH Core)
                [ "Unsafe Worker/Wrapper Split",
                  "For any \"prog :: a\", and given \"wrap :: b -> a\" and \"unwrap :: a -> b\" as arguments, then",
                  "prog = expr  ==>  prog = let f = \\ prog -> expr",
                  "                          in let work = unwrap (f (wrap work))",
                  "                              in wrap work",
                  "Note: the pre-condition \"fix a (wrap . unwrap . f) == fix a f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-split-param" ((\ n wrap unwrap assC -> promoteDefR $ workerWrapperSplitParam n (mkWWAssC assC) wrap unwrap)
                                      :: Int -> CoreString -> CoreString -> RewriteH Core -> RewriteH Core)
                [ "Worker/Wrapper Split - Type Paramater Variant",
                  "For any \"prog :: forall t1 t2 .. tn . a\",",
                  "and given \"wrap :: forall t1 t2 .. tn . b -> a\" and \"unwrap :: forall t1 t2 .. tn . a -> b\" as arguments,",
                  "and a proof of Assumption C (forall t1 t2 .. tn . fix a (wrap t1 t2 .. tn . unwrap t1 t2 .. tn . f) ==> fix a f), then",
                  "prog = expr  ==>  prog = \\ t1 t2 .. tn -> let f = \\ prog -> expr t1 t2 .. tn",
                  "                                            in let work = unwrap t1 t2 .. tn (f (wrap t1 t2  ..tn work))",
                  "                                                in wrap t1 t2 .. tn work"
                ] .+ Introduce .+ Context .+ PreCondition .+ TODO .+ Experiment
         , external "ww-split-param-unsafe" ((\ n wrap unwrap -> promoteDefR $ workerWrapperSplitParam n Nothing wrap unwrap)
                                             :: Int -> CoreString -> CoreString -> RewriteH Core)
                [ "Unsafe Worker/Wrapper Split - Type Paramater Variant",
                  "For any \"prog :: forall t1 t2 .. tn . a\",",
                  "and given \"wrap :: forall t1 t2 .. tn . b -> a\" and \"unwrap :: forall t1 t2 .. tn . a -> b\" as arguments, then",
                  "prog = expr  ==>  prog = \\ t1 t2 .. tn -> let f = \\ prog -> expr t1 t2 .. tn",
                  "                                            in let work = unwrap t1 t2 .. tn (f (wrap t1 t2  ..tn work))",
                  "                                                in wrap t1 t2 .. tn work",
                  "Note: the pre-condition \"forall t1 t2 .. tn . fix a (wrap t1 t2 .. tn . unwrap t1 t2 .. tn . f) == fix a f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition .+ TODO .+ Experiment
         , external "ww-assumption-A" ((\ wrap unwrap assA -> promoteExprBiR $ wwA (Just $ extractR assA) wrap unwrap)
                                       :: CoreString -> CoreString -> RewriteH Core -> BiRewriteH Core)
                [ "Worker/Wrapper Assumption A",
                  "For a \"wrap :: b -> a\" and an \"unwrap :: b -> a\",",
                  "and given a proof of \"wrap (unwrap x)  ==>  x\", then",
                  "wrap (unwrap x)  <==>  x"
                ] .+ Introduce .+ Context
         , external "ww-assumption-B" ((\ wrap unwrap f assB -> promoteExprBiR $ wwB (Just $ extractR assB) wrap unwrap f)
                                       :: CoreString -> CoreString -> CoreString -> RewriteH Core -> BiRewriteH Core)
                [ "Worker/Wrapper Assumption B",
                  "For a \"wrap :: b -> a\", an \"unwrap :: b -> a\", and an \"f :: a -> a\",",
                  "and given a proof of \"wrap (unwrap (f x))  ==>  f x\", then",
                  "wrap (unwrap (f x))  <==>  f x"
                ] .+ Introduce .+ Context
         , external "ww-assumption-C" ((\ wrap unwrap f assC -> promoteExprBiR $ wwC (Just $ extractR assC) wrap unwrap f)
                                       :: CoreString -> CoreString -> CoreString -> RewriteH Core -> BiRewriteH Core)
                [ "Worker/Wrapper Assumption C",
                  "For a \"wrap :: b -> a\", an \"unwrap :: b -> a\", and an \"f :: a -> a\",",
                  "and given a proof of \"fix t (\\ x -> wrap (unwrap (f x)))  ==>  fix t f\", then",
                  "fix t (\\ x -> wrap (unwrap (f x)))  <==>  fix t f"
                ] .+ Introduce .+ Context
         , external "ww-assumption-A-unsafe" ((\ wrap unwrap -> promoteExprBiR $ wwA Nothing wrap unwrap)
                                              :: CoreString -> CoreString -> BiRewriteH Core)
                [ "Unsafe Worker/Wrapper Assumption A",
                  "For a \"wrap :: b -> a\" and an \"unwrap :: b -> a\", then",
                  "wrap (unwrap x)  <==>  x",
                  "Note: only use this if it's true!"
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-assumption-B-unsafe" ((\ wrap unwrap f -> promoteExprBiR $ wwB Nothing wrap unwrap f)
                                              :: CoreString -> CoreString -> CoreString -> BiRewriteH Core)
                [ "Unsafe Worker/Wrapper Assumption B",
                  "For a \"wrap :: b -> a\", an \"unwrap :: b -> a\", and an \"f :: a -> a\" then",
                  "wrap (unwrap (f x))  <==>  f x",
                  "Note: only use this if it's true!"
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-assumption-C-unsafe" ((\ wrap unwrap f -> promoteExprBiR $ wwC Nothing wrap unwrap f)
                                              :: CoreString -> CoreString -> CoreString -> BiRewriteH Core)
                [ "Unsafe Worker/Wrapper Assumption C",
                  "For a \"wrap :: b -> a\", an \"unwrap :: b -> a\", and an \"f :: a -> a\" then",
                  "fix t (\\ x -> wrap (unwrap (f x)))  <==>  fix t f",
                  "Note: only use this if it's true!"
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-AssA-to-AssB" (promoteExprR . wwAssAimpliesAssB . extractR :: RewriteH Core -> RewriteH Core)
                   [ "Convert a proof of worker/wrapper Assumption A into a proof of worker/wrapper Assumption B."
                   ]
         , external "ww-AssB-to-AssC" (promoteExprR . wwAssBimpliesAssC . extractR :: RewriteH Core -> RewriteH Core)
                   [ "Convert a proof of worker/wrapper Assumption B into a proof of worker/wrapper Assumption C."
                   ]
         , external "ww-AssA-to-AssC" (promoteExprR . wwAssAimpliesAssC . extractR :: RewriteH Core -> RewriteH Core)
                   [ "Convert a proof of worker/wrapper Assumption A into a proof of worker/wrapper Assumption C."
                   ]
         , external "ww-generate-fusion" (wwGenerateFusionR :: RewriteH Core)
                   [ "Execute this command on \"work = unwrap (f (wrap work))\" to enable the \"ww-fusion\" rule thereafter.",
                     "Note that this is performed automatically as part of \"ww-split\"."
                   ] .+ Experiment .+ TODO
         ]
  where
    mkWWAssC :: RewriteH Core -> Maybe WWAssumption
    mkWWAssC r = Just (WWAssumption C (extractR r))

--------------------------------------------------------------------------------------------------

data WWAssumptionTag = A | B | C deriving (Eq,Ord,Show,Read)
data WWAssumption = WWAssumption WWAssumptionTag (RewriteH CoreExpr)

--------------------------------------------------------------------------------------------------

-- | For any @f :: a -> a@, and given @wrap :: b -> a@ and @unwrap :: a -> b@ as arguments, then
--   @fix tyA f@  \<==\>  @wrap (fix tyB (\\ b -> unwrap (f (wrap b))))@
workerWrapperFacBR :: Maybe WWAssumption -> CoreExpr -> CoreExpr -> BiRewriteH CoreExpr
workerWrapperFacBR mAss wrap unwrap = beforeBiR (wrapUnwrapTypes wrap unwrap)
                                                (\ (tyA,tyB) -> bidirectional (wwL tyA tyB) wwR)
  where
    wwL :: Type -> Type -> RewriteH CoreExpr
    wwL tyA tyB = prefixFailMsg "worker/wrapper factorisation failed: " $
                  do (tA,f) <- isFixExpr
                     guardMsg (eqType tyA tA) ("wrapper/unwrapper types do not match fix body type.")
                     fromJustM (verifyWWAss wrap unwrap f) mAss
                     b <- constT (newIdH "x" tyB)
                     App wrap <$> mkFix (Lam b (App unwrap (App f (App wrap (Var b)))))

    wwR :: RewriteH CoreExpr
    wwR  =    prefixFailMsg "(reverse) worker/wrapper factorisation failed: " $
              withPatFailMsg "not an application." $
              do App wrap2 fx <- idR
                 withPatFailMsg wrongFixBody $
                   do (_, Lam b (App unwrap1 (App f (App wrap1 (Var b'))))) <- isFixExpr <<< constant fx
                      guardMsg (b == b') wrongFixBody
                      guardMsg (exprEqual wrap wrap2) "given wrapper does not match applied function."
                      guardMsg (exprEqual wrap wrap1) "given wrapper does not match wrapper in body of fix."
                      guardMsg (exprEqual unwrap unwrap1) "given unwrapper does not match unwrapper in body of fix."
                      fromJustM (verifyWWAss wrap unwrap f) mAss
                      mkFix f

    wrongFixBody :: String
    wrongFixBody = "body of fix does not have the form Lam b (App unwrap (App f (App wrap (Var b))))"

-- | For any @f :: a -> a@, and given @wrap :: b -> a@ and @unwrap :: a -> b@ as arguments, then
--   @fix tyA f@  \<==\>  @wrap (fix tyB (\\ b -> unwrap (f (wrap b))))@
workerWrapperFac :: Maybe WWAssumption -> CoreString -> CoreString -> BiRewriteH CoreExpr
workerWrapperFac mAss = parse2beforeBiR (workerWrapperFacBR mAss)

--------------------------------------------------------------------------------------------------

-- | Given @wrap :: b -> a@, @unwrap :: a -> b@ and @work :: b@ as arguments, then
--   @unwrap (wrap work)@  \<==\>  @work@
workerWrapperFusionBR :: Maybe WWAssumption
                      -> CoreExpr                  -- ^ wrap
                      -> CoreExpr                  -- ^ unwrap
                      -> CoreExpr                  -- ^ work
                      -> BiRewriteH CoreExpr
workerWrapperFusionBR mAss wrap unwrap work =
    beforeBiR (prefixFailMsg "worker/wrapper fusion failed: " $
               do (_,tyB) <- wrapUnwrapTypes wrap unwrap
                  guardMsg (exprType work `eqType` tyB) "type of worker does not match types of wrap/unwrap."
                  case mAss of
                    Nothing  -> return ()
                    Just ass -> do Def v_work (App unwrap' (App f (App wrap' work'))) <- constT (lookupDef workLabel)
                                   guardMsg (exprEqual wrap wrap') "wrapper does match original definition of worker."
                                   guardMsg (exprEqual unwrap unwrap') "unwrapper does not match original definition of worker."
                                   guardMsg (exprsEqual [work, work', Var v_work]) "worker does not match original worker."
                                   verifyWWAss wrap unwrap f ass

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


-- Def work' (App unwrap' (App f (App wrap' work''))) <- constT (lookupDef workLabel)


-- | Given @wrap :: b -> a@, @unwrap :: a -> b@ and @work :: b@ as arguments, then
--   @unwrap (wrap work)@  \<==\>  @work@
workerWrapperFusion :: Maybe WWAssumption -> CoreString -> CoreString -> CoreString -> BiRewriteH CoreExpr
workerWrapperFusion mr = parse3beforeBiR (workerWrapperFusionBR mr)

--------------------------------------------------------------------------------------------------

-- Note: The current approach to WW Fusion is a hack.
-- I'm not sure what the best way to approach this is though.
-- An alternative would be to have a generate command that adds ww-fusion to the dictionary, all preconditions verified in advance.
-- That would have to exist at the Shell level though.

-- This isn't entirely safe, as a malicious the user could define a label with this name.
workLabel :: Label
workLabel = "recursive-definition-of-work-for-use-by-ww-fusion"

-- Save the recursive definition of work in the stash, so that we can later verify uses of WW Fusion.
wwGenerateFusionR :: RewriteH Core
wwGenerateFusionR = prefixFailMsg "generate WW fusion failed: " $
                    withPatFailMsg ("definition does not have the form: work = unwrap (f (wrap work))") $
                    do Def work (App _unwrap (App _f (App _wrap (Var work')))) <- projectT
                       guardMsg (work == work') "not a recursive call to worker."
                       rememberR workLabel

--------------------------------------------------------------------------------------------------

-- | \\ wrap unwrap ->  (@prog = expr@  ==>  @prog = let f = \\ prog -> expr in let work = unwrap (f (wrap work)) in wrap work)@
workerWrapperSplitR :: Maybe WWAssumption -> CoreExpr -> CoreExpr -> RewriteH CoreDef
workerWrapperSplitR mAss wrap unwrap =
  let work = TH.mkName "work"
      fx   = TH.mkName "fix"
   in
      fixIntro
      >>> defAllR idR ( appAllR idR (letIntroR "f")
                        >>> letFloatArgR
                        >>> letAllR idR ( forewardT (workerWrapperFacBR mAss wrap unwrap)
                                          >>> appAllR idR ( unfoldNameR fx
                                                            >>> alphaLetWith [work]
                                                            >>> letRecAllR (\ _ -> defAllR idR (betaReduceR >>> letSubstR)
                                                                                   >>> extractR wwGenerateFusionR
                                                                           )
                                                                           idR
                                                          )
                                          >>> letFloatArgR
                                        )
                      )

-- | \\ wrap unwrap ->  (@prog = expr@  ==>  @prog = let f = \\ prog -> expr in let work = unwrap (f (wrap work)) in wrap work)@
workerWrapperSplit :: Maybe WWAssumption -> CoreString -> CoreString -> RewriteH CoreDef
workerWrapperSplit mAss wrapS unwrapS = (parseCoreExprT wrapS &&& parseCoreExprT unwrapS) >>= uncurry (workerWrapperSplitR mAss)

-- | As 'workerWrapperSplit' but performs the static-argument transformation for @n@ type paramaters first, providing these types as arguments to all calls of wrap and unwrap.
--   This is useful if the expression, and wrap and unwrap, all have a @forall@ type.
workerWrapperSplitParam :: Int -> Maybe WWAssumption -> CoreString -> CoreString -> RewriteH CoreDef
workerWrapperSplitParam 0 = workerWrapperSplit
workerWrapperSplitParam n = \ mAss wrapS unwrapS ->
                            prefixFailMsg "worker/wrapper split (forall variant) failed: " $
                            do guardMsg (n == 1) "currently only supports 1 type paramater."
                               withPatFailMsg "right-hand-side of definition does not have the form: Lam t e" $
                                 do Def _ (Lam t _) <- idR
                                    guardMsg (isTyVar t) "first argument is not a type."
                                    let splitAtDefR :: RewriteH Core
                                        splitAtDefR = do p <- considerConstructT Definition
                                                         localPathR p $ promoteR $ do wrap   <- parseCoreExprT wrapS
                                                                                      unwrap <- parseCoreExprT unwrapS
                                                                                      let ty = Type (TyVarTy t)
                                                                                      workerWrapperSplitR mAss (App wrap ty) (App unwrap ty)
                                    staticArgR >>> extractR splitAtDefR

--------------------------------------------------------------------------------------------------

-- | Convert a proof of WW Assumption A into a proof of WW Assumption B.
wwAssAimpliesAssB :: RewriteH CoreExpr -> RewriteH CoreExpr
wwAssAimpliesAssB = id

-- | Convert a proof of WW Assumption B into a proof of WW Assumption C.
wwAssBimpliesAssC :: RewriteH CoreExpr -> RewriteH CoreExpr
wwAssBimpliesAssC assB = appAllR idR (lamAllR idR assB >>> etaReduceR)

-- | Convert a proof of WW Assumption A into a proof of WW Assumption C.
wwAssAimpliesAssC :: RewriteH CoreExpr -> RewriteH CoreExpr
wwAssAimpliesAssC =  wwAssBimpliesAssC . wwAssAimpliesAssB

--------------------------------------------------------------------------------------------------

-- | @wrap (unwrap x)@  \<==\>  @x@
wwAssA :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption B
       -> CoreExpr                  -- ^ wrap
       -> CoreExpr                  -- ^ unwrap
       -> BiRewriteH CoreExpr
wwAssA mr wrap unwrap = beforeBiR (do fromJustM (verifyAssA wrap unwrap) mr
                                      wrapUnwrapTypes wrap unwrap
                                  )
                                  (\ (tyA,_) -> bidirectional wwAL (wwAR tyA))
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
wwA :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption A
    -> CoreString                -- ^ wrap
    -> CoreString                -- ^ unwrap
    -> BiRewriteH CoreExpr
wwA mr = parse2beforeBiR (wwAssA mr)

-- | @wrap (unwrap (f x))@  \<==\>  @f x@
wwAssB :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption B
       -> CoreExpr                  -- ^ wrap
       -> CoreExpr                  -- ^ unwrap
       -> CoreExpr                  -- ^ f
       -> BiRewriteH CoreExpr
wwAssB mr wrap unwrap f = beforeBiR (fromJustM (verifyAssB wrap unwrap f) mr)
                                    (\ () -> bidirectional wwBL wwBR)
  where
    assA :: BiRewriteH CoreExpr
    assA = wwAssA Nothing wrap unwrap

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
wwB :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption B
    -> CoreString                -- ^ wrap
    -> CoreString                -- ^ unwrap
    -> CoreString                -- ^ f
    -> BiRewriteH CoreExpr
wwB mr = parse3beforeBiR (wwAssB mr)

-- | @fix t (\ x -> wrap (unwrap (f x)))@  \<==\>  @fix t f@
wwAssC :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption C
       -> CoreExpr                  -- ^ wrap
       -> CoreExpr                  -- ^ unwrap
       -> CoreExpr                  -- ^ f
       -> BiRewriteH CoreExpr
wwAssC mr wrap unwrap f = beforeBiR (do fromJustM (verifyAssC wrap unwrap f) mr
                                        isFixExpr)
                                    (\ _ -> bidirectional wwCL wwCR)
  where
    assB :: BiRewriteH CoreExpr
    assB = wwAssB Nothing wrap unwrap f

    wwCL :: RewriteH CoreExpr
    wwCL = appAllR idR (lamAllR idR (forewardT assB) >>> etaReduceR)

    wwCR :: RewriteH CoreExpr
    wwCR = appAllR idR (etaExpandR "x" >>> lamAllR idR (backwardT assB))

-- | @fix t (\ x -> wrap (unwrap (f x)))@  \<==\>  @fix t f@
wwC :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption C
    -> CoreString                -- ^ wrap
    -> CoreString                -- ^ unwrap
    -> CoreString                -- ^ f
    -> BiRewriteH CoreExpr
wwC mr = parse3beforeBiR (wwAssC mr)

--------------------------------------------------------------------------------------------------

verifyWWAss :: CoreExpr        -- ^ wrap
            -> CoreExpr        -- ^ unwrap
            -> CoreExpr        -- ^ f
            -> WWAssumption
            -> TranslateH x ()
verifyWWAss wrap unwrap f (WWAssumption tag ass) =
    case tag of
      A -> verifyAssA wrap unwrap ass
      B -> verifyAssB wrap unwrap f ass
      C -> verifyAssC wrap unwrap f ass

verifyAssA :: CoreExpr          -- ^ wrap
           -> CoreExpr          -- ^ unwrap
           -> RewriteH CoreExpr -- ^ WW Assumption A
           -> TranslateH x ()
verifyAssA wrap unwrap assA =
  prefixFailMsg ("verification of worker/wrapper Assumption A failed: ") $
  do (tyA,_) <- wrapUnwrapTypes wrap unwrap
     a       <- constT (newIdH "a" tyA)
     let lhs = App wrap (App unwrap (Var a))
         rhs = Var a
     verifyEqualityProofT lhs rhs assA

verifyAssB :: CoreExpr          -- ^ wrap
           -> CoreExpr          -- ^ unwrap
           -> CoreExpr          -- ^ f
           -> RewriteH CoreExpr -- ^ WW Assumption B
           -> TranslateH x ()
verifyAssB wrap unwrap f assB =
  prefixFailMsg ("verification of worker/wrapper assumption B failed: ") $
  do (tyA,_) <- wrapUnwrapTypes wrap unwrap
     a      <- constT (newIdH "a" tyA)
     let lhs = App wrap (App unwrap (App f (Var a)))
         rhs = App f (Var a)
     verifyEqualityProofT lhs rhs assB

verifyAssC :: CoreExpr          -- ^ wrap
           -> CoreExpr          -- ^ unwrap
           -> CoreExpr          -- ^ f
           -> RewriteH CoreExpr -- ^ WW Assumption C
           -> TranslateH a ()
verifyAssC wrap unwrap f assC =
  prefixFailMsg ("verification of worker/wrapper assumption C failed: ") $
  do (tyA,_) <- wrapUnwrapTypes wrap unwrap
     a       <- constT (newIdH "a" tyA)
     rhs     <- mkFix f
     lhs     <- mkFix (Lam a (App wrap (App unwrap (App f (Var a)))))
     verifyEqualityProofT lhs rhs assC

-- | Given two expressions, and a rewrite from the former to the latter, verify that rewrite.
verifyEqualityProofT :: CoreExpr -> CoreExpr -> RewriteH CoreExpr -> TranslateH a ()
verifyEqualityProofT sourceExpr targetExpr r =
  prefixFailMsg "equality verification failed: " $
  do resultExpr <- r <<< return sourceExpr
     guardMsg (exprEqual targetExpr resultExpr) "result of running proof on lhs of equality does not match rhs of equality."

--------------------------------------------------------------------------------------------------

wrapUnwrapTypes :: MonadCatch m => CoreExpr -> CoreExpr -> m (Type,Type)
wrapUnwrapTypes wrap unwrap = setFailMsg "given expressions have the wrong types to form a valid wrap/unwrap pair." $
                              funsWithInverseTypes unwrap wrap

--------------------------------------------------------------------------------------------------

parse2beforeBiR :: (CoreExpr -> CoreExpr -> BiRewriteH a) -> CoreString -> CoreString -> BiRewriteH a
parse2beforeBiR f s1 s2 = beforeBiR (parseCoreExprT s1 &&& parseCoreExprT s2) (uncurry f)

parse3beforeBiR :: (CoreExpr -> CoreExpr -> CoreExpr -> BiRewriteH a) -> CoreString -> CoreString -> CoreString -> BiRewriteH a
parse3beforeBiR f s1 s2 s3 = beforeBiR ((parseCoreExprT s1 &&& parseCoreExprT s2) &&& parseCoreExprT s3) ((uncurry.uncurry) f)

--------------------------------------------------------------------------------------------------

fromJustM :: Monad m => (a -> m ()) -> Maybe a -> m ()
fromJustM f = maybe (return ()) f

--------------------------------------------------------------------------------------------------
