{-# LANGUAGE NoImplicitPrelude #-}

module HERMIT.Dictionary.WorkerWrapper.Fix
    ( -- * The Worker/Wrapper Transformation
      -- | Note that many of these operations require 'Data.Function.fix' to be in scope.
      HERMIT.Dictionary.WorkerWrapper.Fix.externals
    , wwFacBR
    , wwSplitR
    , wwSplitStaticArg
    , wwGenerateFusionT
    , wwFusionBR
    , wwAssA
    , wwAssB
    , wwAssC
    , wwAssAimpliesAssB
    , wwAssBimpliesAssC
    , wwAssAimpliesAssC
    ) where

import Control.Arrow

import Data.String (fromString)

import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure hiding ((<$>))
import HERMIT.Lemma
import HERMIT.Monad
import HERMIT.Name
import HERMIT.ParserCore
import HERMIT.Utilities

import HERMIT.Dictionary.AlphaConversion
import HERMIT.Dictionary.Common
import HERMIT.Dictionary.FixPoint
import HERMIT.Dictionary.Function
import HERMIT.Dictionary.Local
import HERMIT.Dictionary.Navigation
import HERMIT.Dictionary.Reasoning
import HERMIT.Dictionary.Unfold

import HERMIT.Dictionary.WorkerWrapper.Common

import Prelude.Compat

--------------------------------------------------------------------------------------------------

-- | Externals for manipulating fixed points, and for the worker/wrapper transformation.
externals ::  [External]
externals =
         [
           external "ww-factorisation" ((\ wrap unwrap assC -> promoteExprBiR $ wwFac (mkWWAssC assC) wrap unwrap)
                                          :: CoreString -> CoreString -> RewriteH LCore -> BiRewriteH LCore)
                [ "Worker/Wrapper Factorisation",
                  "For any \"f :: A -> A\", and given \"wrap :: B -> A\" and \"unwrap :: A -> B\" as arguments,",
                  "and a proof of Assumption C (fix A (\\ a -> wrap (unwrap (f a))) ==> fix A f), then",
                  "fix A f  ==>  wrap (fix B (\\ b -> unwrap (f (wrap b))))"
                ] .+ Introduce .+ Context
         , external "ww-factorisation-unsafe" ((\ wrap unwrap -> promoteExprBiR $ wwFac Nothing wrap unwrap)
                                               :: CoreString -> CoreString -> BiRewriteH LCore)
                [ "Unsafe Worker/Wrapper Factorisation",
                  "For any \"f :: A -> A\", and given \"wrap :: B -> A\" and \"unwrap :: A -> B\" as arguments, then",
                  "fix A f  <==>  wrap (fix B (\\ b -> unwrap (f (wrap b))))",
                  "Note: the pre-condition \"fix A (\\ a -> wrap (unwrap (f a))) == fix A f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-split" ((\ wrap unwrap assC -> promoteDefR $ wwSplit (mkWWAssC assC) wrap unwrap)
                                  :: CoreString -> CoreString -> RewriteH LCore -> RewriteH LCore)
                [ "Worker/Wrapper Split",
                  "For any \"prog :: A\", and given \"wrap :: B -> A\" and \"unwrap :: A -> B\" as arguments,",
                  "and a proof of Assumption C (fix A (\\ a -> wrap (unwrap (f a))) ==> fix A f), then",
                  "prog = expr  ==>  prog = let f = \\ prog -> expr",
                  "                          in let work = unwrap (f (wrap work))",
                  "                              in wrap work"
                ] .+ Introduce .+ Context
         , external "ww-split-unsafe" ((\ wrap unwrap -> promoteDefR $ wwSplit Nothing wrap unwrap)
                                       :: CoreString -> CoreString -> RewriteH LCore)
                [ "Unsafe Worker/Wrapper Split",
                  "For any \"prog :: A\", and given \"wrap :: B -> A\" and \"unwrap :: A -> B\" as arguments, then",
                  "prog = expr  ==>  prog = let f = \\ prog -> expr",
                  "                          in let work = unwrap (f (wrap work))",
                  "                              in wrap work",
                  "Note: the pre-condition \"fix A (wrap . unwrap . f) == fix A f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-split-static-arg" ((\ n is wrap unwrap assC -> promoteDefR $ wwSplitStaticArg n is (mkWWAssC assC) wrap unwrap)
                                      :: Int -> [Int] -> CoreString -> CoreString -> RewriteH LCore -> RewriteH LCore)
                [ "Worker/Wrapper Split - Static Argument Variant",
                  "Perform the static argument transformation on the first n arguments, then perform the worker/wrapper split,",
                  "applying the given wrap and unwrap functions to the specified (by index) static arguments before use."
                ] .+ Introduce .+ Context
         , external "ww-split-static-arg-unsafe" ((\ n is wrap unwrap -> promoteDefR $ wwSplitStaticArg n is Nothing wrap unwrap)
                                      :: Int -> [Int] -> CoreString -> CoreString -> RewriteH LCore)
                [ "Unsafe Worker/Wrapper Split - Static Argument Variant",
                  "Perform the static argument transformation on the first n arguments, then perform the (unsafe) worker/wrapper split,",
                  "applying the given wrap and unwrap functions to the specified (by index) static arguments before use."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-assumption-A" ((\ wrap unwrap assA -> promoteExprBiR $ wwA (Just $ extractR assA) wrap unwrap)
                                       :: CoreString -> CoreString -> RewriteH LCore -> BiRewriteH LCore)
                [ "Worker/Wrapper Assumption A",
                  "For a \"wrap :: B -> A\" and an \"unwrap :: A -> B\",",
                  "and given a proof of \"wrap (unwrap a) ==> a\", then",
                  "wrap (unwrap a)  <==>  a"
                ] .+ Introduce .+ Context
         , external "ww-assumption-B" ((\ wrap unwrap f assB -> promoteExprBiR $ wwB (Just $ extractR assB) wrap unwrap f)
                                       :: CoreString -> CoreString -> CoreString -> RewriteH LCore -> BiRewriteH LCore)
                [ "Worker/Wrapper Assumption B",
                  "For a \"wrap :: B -> A\", an \"unwrap :: A -> B\", and an \"f :: A -> A\",",
                  "and given a proof of \"wrap (unwrap (f a)) ==> f a\", then",
                  "wrap (unwrap (f a))  <==>  f a"
                ] .+ Introduce .+ Context
         , external "ww-assumption-C" ((\ wrap unwrap f assC -> promoteExprBiR $ wwC (Just $ extractR assC) wrap unwrap f)
                                       :: CoreString -> CoreString -> CoreString -> RewriteH LCore -> BiRewriteH LCore)
                [ "Worker/Wrapper Assumption C",
                  "For a \"wrap :: B -> A\", an \"unwrap :: A -> B\", and an \"f :: A -> A\",",
                  "and given a proof of \"fix A (\\ a -> wrap (unwrap (f a))) ==> fix A f\", then",
                  "fix A (\\ a -> wrap (unwrap (f a)))  <==>  fix A f"
                ] .+ Introduce .+ Context
         , external "ww-assumption-A-unsafe" ((\ wrap unwrap -> promoteExprBiR $ wwA Nothing wrap unwrap)
                                              :: CoreString -> CoreString -> BiRewriteH LCore)
                [ "Unsafe Worker/Wrapper Assumption A",
                  "For a \"wrap :: B -> A\" and an \"unwrap :: A -> B\", then",
                  "wrap (unwrap a)  <==>  a",
                  "Note: only use this if it's true!"
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-assumption-B-unsafe" ((\ wrap unwrap f -> promoteExprBiR $ wwB Nothing wrap unwrap f)
                                              :: CoreString -> CoreString -> CoreString -> BiRewriteH LCore)
                [ "Unsafe Worker/Wrapper Assumption B",
                  "For a \"wrap :: B -> A\", an \"unwrap :: A -> B\", and an \"f :: A -> A\", then",
                  "wrap (unwrap (f a))  <==>  f a",
                  "Note: only use this if it's true!"
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-assumption-C-unsafe" ((\ wrap unwrap f -> promoteExprBiR $ wwC Nothing wrap unwrap f)
                                              :: CoreString -> CoreString -> CoreString -> BiRewriteH LCore)
                [ "Unsafe Worker/Wrapper Assumption C",
                  "For a \"wrap :: B -> A\", an \"unwrap :: A -> B\", and an \"f :: A -> A\", then",
                  "fix A (\\ a -> wrap (unwrap (f a)))  <==>  fix A f",
                  "Note: only use this if it's true!"
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-AssA-to-AssB" (promoteExprR . wwAssAimpliesAssB . extractR :: RewriteH LCore -> RewriteH LCore)
                   [ "Convert a proof of worker/wrapper Assumption A into a proof of worker/wrapper Assumption B."
                   ]
         , external "ww-AssB-to-AssC" (promoteExprR . wwAssBimpliesAssC . extractR :: RewriteH LCore -> RewriteH LCore)
                   [ "Convert a proof of worker/wrapper Assumption B into a proof of worker/wrapper Assumption C."
                   ]
         , external "ww-AssA-to-AssC" (promoteExprR . wwAssAimpliesAssC . extractR :: RewriteH LCore -> RewriteH LCore)
                   [ "Convert a proof of worker/wrapper Assumption A into a proof of worker/wrapper Assumption C."
                   ]
         , external "ww-generate-fusion" (wwGenerateFusionT . mkWWAssC :: RewriteH LCore -> TransformH LCore ())
                   [ "Given a proof of Assumption C (fix A (\\ a -> wrap (unwrap (f a))) ==> fix A f), then",
                     "execute this command on \"work = unwrap (f (wrap work))\" to enable the \"ww-fusion\" rule thereafter.",
                     "Note that this is performed automatically as part of \"ww-split\"."
                   ] .+ Experiment .+ TODO
         , external "ww-generate-fusion-unsafe" (wwGenerateFusionT Nothing :: TransformH LCore ())
                   [ "Execute this command on \"work = unwrap (f (wrap work))\" to enable the \"ww-fusion\" rule thereafter.",
                     "The precondition \"fix A (wrap . unwrap . f) == fix A f\" is expected to hold.",
                     "Note that this is performed automatically as part of \"ww-split\"."
                   ] .+ Experiment .+ TODO
         , external "ww-fusion" (promoteExprBiR wwFusion :: BiRewriteH LCore)
                [ "Worker/Wrapper Fusion",
                  "unwrap (wrap work)  <==>  work",
                  "Note: you are required to have previously executed the command \"ww-generate-fusion\" on the definition",
                  "      work = unwrap (f (wrap work))"
                ] .+ Introduce .+ Context .+ PreCondition .+ TODO
         ]
  where
    mkWWAssC :: RewriteH LCore -> Maybe WWAssumption
    mkWWAssC r = Just (WWAssumption C (extractR r))

--------------------------------------------------------------------------------------------------

-- | For any @f :: A -> A@, and given @wrap :: B -> A@ and @unwrap :: A -> B@ as arguments, then
--   @fix A f@  \<==\>  @wrap (fix B (\\ b -> unwrap (f (wrap b))))@
wwFacBR :: Maybe WWAssumption -> CoreExpr -> CoreExpr -> BiRewriteH CoreExpr
wwFacBR mAss wrap unwrap = beforeBiR (wrapUnwrapTypes wrap unwrap)
                                                (\ (tyA,tyB) -> bidirectional (wwL tyA tyB) wwR)
  where
    wwL :: Type -> Type -> RewriteH CoreExpr
    wwL tyA tyB = prefixFailMsg "worker/wrapper factorisation failed: " $
                  do (tA,f) <- isFixExprT
                     guardMsg (eqType tyA tA) ("wrapper/unwrapper types do not match fix body type.")
                     whenJust (verifyWWAss wrap unwrap f) mAss
                     b <- constT (newIdH "x" tyB)
                     App wrap <$> buildFixT (Lam b (App unwrap (App f (App wrap (Var b)))))

    wwR :: RewriteH CoreExpr
    wwR  =    prefixFailMsg "(reverse) worker/wrapper factorisation failed: " $
              withPatFailMsg "not an application." $
              do App wrap2 fx <- idR
                 withPatFailMsg wrongFixBody $
                   do (_, Lam b (App unwrap1 (App f (App wrap1 (Var b'))))) <- isFixExprT <<< constant fx
                      guardMsg (b == b') wrongFixBody
                      guardMsg (equivalentBy exprAlphaEq [wrap, wrap1, wrap2]) "wrappers do not match."
                      guardMsg (exprAlphaEq unwrap unwrap1) "unwrappers do not match."
                      whenJust (verifyWWAss wrap unwrap f) mAss
                      buildFixT f

    wrongFixBody :: String
    wrongFixBody = "body of fix does not have the form Lam b (App unwrap (App f (App wrap (Var b))))"

-- | For any @f :: A -> A@, and given @wrap :: B -> A@ and @unwrap :: A -> B@ as arguments, then
--   @fix A f@  \<==\>  @wrap (fix B (\\ b -> unwrap (f (wrap b))))@
wwFac :: Maybe WWAssumption -> CoreString -> CoreString -> BiRewriteH CoreExpr
wwFac mAss = parse2beforeBiR (wwFacBR mAss)

--------------------------------------------------------------------------------------------------

-- | Given @wrap :: B -> A@, @unwrap :: A -> B@ and @work :: B@ as arguments, then
--   @unwrap (wrap work)@  \<==\>  @work@
wwFusionBR :: BiRewriteH CoreExpr
wwFusionBR =
    beforeBiR (prefixFailMsg "worker/wrapper fusion failed: " $
               withPatFailMsg "malformed WW Fusion rule." $
               do Equiv w (App unwrap (App _f (App wrap w'))) <- constT (lemmaC <$> findLemma workLabel)
                  guardMsg (exprSyntaxEq w w') "malformed WW Fusion rule."
                  return (wrap,unwrap,w)
              )
              (\ (wrap,unwrap,work) -> bidirectional (fusL wrap unwrap work) (fusR wrap unwrap work))
  where
    fusL :: CoreExpr -> CoreExpr -> CoreExpr -> RewriteH CoreExpr
    fusL wrap unwrap work =
           prefixFailMsg "worker/wrapper fusion failed: " $
           withPatFailMsg (wrongExprForm "unwrap (wrap work)") $
           do App unwrap' (App wrap' work') <- idR
              guardMsg (exprAlphaEq wrap wrap') "wrapper does not match."
              guardMsg (exprAlphaEq unwrap unwrap') "unwrapper does not match."
              guardMsg (exprAlphaEq work work') "worker does not match."
              return work

    fusR :: CoreExpr -> CoreExpr -> CoreExpr -> RewriteH CoreExpr
    fusR wrap unwrap work =
           prefixFailMsg "(reverse) worker/wrapper fusion failed: " $
           do work' <- idR
              guardMsg (exprAlphaEq work work') "worker does not match."
              return $ App unwrap (App wrap work)


-- | Given @wrap :: B -> A@, @unwrap :: A -> B@ and @work :: B@ as arguments, then
--   @unwrap (wrap work)@  \<==\>  @work@
wwFusion :: BiRewriteH CoreExpr
wwFusion = wwFusionBR

--------------------------------------------------------------------------------------------------

-- | Save the recursive definition of work in the stash, so that we can later verify uses of 'wwFusionBR'.
--   Must be applied to a definition of the form: @work = unwrap (f (wrap work))@
--   Note that this is performed automatically as part of 'wwSplitR'.
wwGenerateFusionT :: Maybe WWAssumption -> TransformH LCore ()
wwGenerateFusionT mAss =
    prefixFailMsg "generate WW fusion failed: " $
    withPatFailMsg wrongForm $
    do Def w e@(App unwrap (App f (App wrap (Var w')))) <- projectT
       guardMsg (w == w') wrongForm
       whenJust (verifyWWAss wrap unwrap f) mAss
       insertLemmaT workLabel $ Lemma (Equiv (varToCoreExpr w) e) Proven NotUsed
  where
    wrongForm = "definition does not have the form: work = unwrap (f (wrap work))"

--------------------------------------------------------------------------------------------------

-- | \\ wrap unwrap ->  (@prog = expr@  ==>  @prog = let f = \\ prog -> expr in let work = unwrap (f (wrap work)) in wrap work)@
wwSplitR :: Maybe WWAssumption -> CoreExpr -> CoreExpr -> RewriteH CoreDef
wwSplitR mAss wrap unwrap =
      fixIntroRecR
      >>> defAllR idR ( appAllR idR (letIntroR "f")
                        >>> letFloatArgR
                        >>> letAllR idR ( forwardT (wwFacBR mAss wrap unwrap)
                                          >>> appAllR idR ( unfoldNameR (fromString "Data.Function.fix")
                                                            >>> alphaLetWithR ["work"]
                                                            >>> letRecAllR (\ _ -> defAllR idR (betaReduceR >>> letNonRecSubstR)
                                                                                   >>> (extractT (wwGenerateFusionT mAss) >> idR)
                                                                           )
                                                                           idR
                                                          )
                                          >>> letFloatArgR
                                        )
                      )

-- | \\ wrap unwrap ->  (@prog = expr@  ==>  @prog = let f = \\ prog -> expr in let work = unwrap (f (wrap work)) in wrap work)@
wwSplit :: Maybe WWAssumption -> CoreString -> CoreString -> RewriteH CoreDef
wwSplit mAss wrapS unwrapS = (parseCoreExprT wrapS &&& parseCoreExprT unwrapS) >>= uncurry (wwSplitR mAss)

-- | As 'wwSplit' but performs the static-argument transformation for @n@ static arguments first, and optionally provides some of those arguments (specified by index) to all calls of wrap and unwrap.
--   This is useful if, for example, the expression, and wrap and unwrap, all have a @forall@ type.
wwSplitStaticArg :: Int -> [Int] -> Maybe WWAssumption -> CoreString -> CoreString -> RewriteH CoreDef
wwSplitStaticArg 0 _  = wwSplit
wwSplitStaticArg n is = \ mAss wrapS unwrapS ->
                            prefixFailMsg "worker/wrapper split (static argument variant) failed: " $
                            do guardMsg (all (< n) is) "arguments for wrap and unwrap must be chosen from the statically transformed arguments."
                               bs <- defT successT (arr collectBinders) (\ () -> take n . fst)
                               let args = varsToCoreExprs [ b | (i,b) <- zip [0..] bs, i `elem` is ]

                               staticArgPosR [0..(n-1)] >>> defAllR idR
                                                                    (let wwSplitArgsR :: RewriteH CoreDef
                                                                         wwSplitArgsR = do wrap   <- parseCoreExprT wrapS
                                                                                           unwrap <- parseCoreExprT unwrapS
                                                                                           wwSplitR mAss (mkCoreApps wrap args) (mkCoreApps unwrap args)
                                                                      in
                                                                         extractR $ do p <- considerConstructT LetExpr
                                                                                       localPathR p $ promoteExprR (letRecAllR (const wwSplitArgsR) idR >>> letSubstR)
                                                                    )


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

-- | @wrap (unwrap a)@  \<==\>  @a@
wwAssA :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption A
       -> CoreExpr                  -- ^ wrap
       -> CoreExpr                  -- ^ unwrap
       -> BiRewriteH CoreExpr
wwAssA mr wrap unwrap = beforeBiR (do whenJust (verifyAssA wrap unwrap) mr
                                      wrapUnwrapTypes wrap unwrap
                                  )
                                  (\ (tyA,_) -> bidirectional wwAL (wwAR tyA))
  where
    wwAL :: RewriteH CoreExpr
    wwAL = withPatFailMsg (wrongExprForm "App wrap (App unwrap x)") $
           do App wrap' (App unwrap' x) <- idR
              guardMsg (exprAlphaEq wrap wrap')     "given wrapper does not match wrapper in expression."
              guardMsg (exprAlphaEq unwrap unwrap') "given unwrapper does not match unwrapper in expression."
              return x

    wwAR :: Type -> RewriteH CoreExpr
    wwAR tyA = do x <- idR
                  guardMsg (exprKindOrType x `eqType` tyA) "type of expression does not match types of wrap/unwrap."
                  return $ App wrap (App unwrap x)

-- | @wrap (unwrap a)@  \<==\>  @a@
wwA :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption A
    -> CoreString                -- ^ wrap
    -> CoreString                -- ^ unwrap
    -> BiRewriteH CoreExpr
wwA mr = parse2beforeBiR (wwAssA mr)

-- | @wrap (unwrap (f a))@  \<==\>  @f a@
wwAssB :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption B
       -> CoreExpr                  -- ^ wrap
       -> CoreExpr                  -- ^ unwrap
       -> CoreExpr                  -- ^ f
       -> BiRewriteH CoreExpr
wwAssB mr wrap unwrap f = beforeBiR (whenJust (verifyAssB wrap unwrap f) mr)
                                    (\ () -> bidirectional wwBL wwBR)
  where
    assA :: BiRewriteH CoreExpr
    assA = wwAssA Nothing wrap unwrap

    wwBL :: RewriteH CoreExpr
    wwBL = withPatFailMsg (wrongExprForm "App wrap (App unwrap (App f a))") $
           do App _ (App _ (App f' _)) <- idR
              guardMsg (exprAlphaEq f f') "given body function does not match expression."
              forwardT assA

    wwBR :: RewriteH CoreExpr
    wwBR = withPatFailMsg (wrongExprForm "App f a") $
           do App f' _ <- idR
              guardMsg (exprAlphaEq f f') "given body function does not match expression."
              backwardT assA

-- | @wrap (unwrap (f a))@  \<==\>  @f a@
wwB :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption B
    -> CoreString                -- ^ wrap
    -> CoreString                -- ^ unwrap
    -> CoreString                -- ^ f
    -> BiRewriteH CoreExpr
wwB mr = parse3beforeBiR (wwAssB mr)

-- | @fix A (\ a -> wrap (unwrap (f a)))@  \<==\>  @fix A f@
wwAssC :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption C
       -> CoreExpr                  -- ^ wrap
       -> CoreExpr                  -- ^ unwrap
       -> CoreExpr                  -- ^ f
       -> BiRewriteH CoreExpr
wwAssC mr wrap unwrap f = beforeBiR (do _ <- isFixExprT
                                        whenJust (verifyAssC wrap unwrap f) mr
                                    )
                                    (\ () -> bidirectional wwCL wwCR)
  where
    assB :: BiRewriteH CoreExpr
    assB = wwAssB Nothing wrap unwrap f

    wwCL :: RewriteH CoreExpr
    wwCL = wwAssBimpliesAssC (forwardT assB)

    wwCR :: RewriteH CoreExpr
    wwCR = appAllR idR (etaExpandR "a" >>> lamAllR idR (backwardT assB))

-- | @fix A (\ a -> wrap (unwrap (f a)))@  \<==\>  @fix A f@
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
            -> TransformH x ()
verifyWWAss wrap unwrap f (WWAssumption tag ass) =
    case tag of
      A -> verifyAssA wrap unwrap ass
      B -> verifyAssB wrap unwrap f ass
      C -> verifyAssC wrap unwrap f ass

verifyAssA :: CoreExpr          -- ^ wrap
           -> CoreExpr          -- ^ unwrap
           -> RewriteH CoreExpr -- ^ WW Assumption A
           -> TransformH x ()
verifyAssA wrap unwrap assA =
  prefixFailMsg ("verification of worker/wrapper Assumption A failed: ") $
  do _ <- wrapUnwrapTypes wrap unwrap -- this check is redundant, but will produce a better error message
     verifyRetractionT wrap unwrap assA

verifyAssB :: CoreExpr          -- ^ wrap
           -> CoreExpr          -- ^ unwrap
           -> CoreExpr          -- ^ f
           -> RewriteH CoreExpr -- ^ WW Assumption B
           -> TransformH x ()
verifyAssB wrap unwrap f assB =
  prefixFailMsg ("verification of worker/wrapper assumption B failed: ") $
  do (tyA,_) <- wrapUnwrapTypes wrap unwrap
     a       <- constT (newIdH "a" tyA)
     let lhs = App wrap (App unwrap (App f (Var a)))
         rhs = App f (Var a)
     verifyEqualityLeftToRightT lhs rhs assB

verifyAssC :: CoreExpr          -- ^ wrap
           -> CoreExpr          -- ^ unwrap
           -> CoreExpr          -- ^ f
           -> RewriteH CoreExpr -- ^ WW Assumption C
           -> TransformH a ()
verifyAssC wrap unwrap f assC =
  prefixFailMsg ("verification of worker/wrapper assumption C failed: ") $
  do (tyA,_) <- wrapUnwrapTypes wrap unwrap
     a       <- constT (newIdH "a" tyA)
     rhs     <- buildFixT f
     lhs     <- buildFixT (Lam a (App wrap (App unwrap (App f (Var a)))))
     verifyEqualityLeftToRightT lhs rhs assC

--------------------------------------------------------------------------------------------------

wrapUnwrapTypes :: MonadCatch m => CoreExpr -> CoreExpr -> m (Type,Type)
wrapUnwrapTypes wrap unwrap = setFailMsg "given expressions have the wrong types to form a valid wrap/unwrap pair." $
                              funExprsWithInverseTypes unwrap wrap

--------------------------------------------------------------------------------------------------
