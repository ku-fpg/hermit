{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}

module HERMIT.Dictionary.WorkerWrapper.FixResult
    ( -- * The Worker/Wrapper Transformation (Result Variant)
      -- | Note that many of these operations require 'Data.Function.fix' to be in scope.
      HERMIT.Dictionary.WorkerWrapper.FixResult.externals
    , wwResultFacBR
    , wwResultSplitR
    , wwResultSplitStaticArg
    , wwResultGenerateFusionT
    , wwResultFusionBR
    , wwResultAssA
    , wwResultAssB
    , wwResultAssC
    , wwA
    , wwB
    , wwC
    , wwResultAssAimpliesAssB
    , wwResultAssBimpliesAssC
    , wwResultAssAimpliesAssC
    , wwFusion
    -- ** Exported for hermit-shell:
    , wwResultSplit
    ) where

import Prelude hiding (abs)

import Control.Arrow

import Data.String (fromString)

import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure 
import HERMIT.Lemma
import HERMIT.Monad
import HERMIT.Name
import HERMIT.ParserCore
import HERMIT.Utilities

import HERMIT.Dictionary.AlphaConversion
import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Function
import HERMIT.Dictionary.Local
import HERMIT.Dictionary.Navigation
import HERMIT.Dictionary.FixPoint
import HERMIT.Dictionary.Reasoning
import HERMIT.Dictionary.Unfold

import HERMIT.Dictionary.WorkerWrapper.Common

import HERMIT.Exception

--------------------------------------------------------------------------------------------------

-- | Externals for manipulating fixed points, and for the worker/wrapper transformation.
externals ::  [External]
externals =
         [
           external "ww-result-factorisation" ((\ abs rep assC -> promoteExprBiR $ wwFac (mkWWAssC assC) abs rep)
                                          :: CoreString -> CoreString -> RewriteH LCore -> BiRewriteH LCore)
                [ "Worker/Wrapper Factorisation (Result Variant)",
                  "For any \"f :: (X -> A) -> (X -> A)\", and given \"abs :: B -> A\" and \"rep :: A -> B\" as arguments,",
                  "and a proof of Assumption C (fix (X -> A) (\\ h x -> abs (rep (f h x))) ==> fix (X->A) f), then",
                  "fix (X->A) f  ==>  \\ x1 -> abs (fix (X->B) (\\ h x2 -> rep (f (\\ x3 -> abs (h x3)) x2)) x1"
                ] .+ Introduce .+ Context
         , external "ww-result-factorisation-unsafe" ((\ abs rep -> promoteExprBiR $ wwFac Nothing abs rep)
                                               :: CoreString -> CoreString -> BiRewriteH LCore)
                [ "Unsafe Worker/Wrapper Factorisation (Result Variant)",
                  "For any \"f :: (X -> A) -> (X -> A)\", and given \"abs :: B -> A\" and \"rep :: A -> B\" as arguments, then",
                  "fix (X->A) f  ==>  \\ x1 -> abs (fix (X->B) (\\ h x2 -> rep (f (\\ x3 -> abs (h x3)) x2)) x1",
                  "Note: the pre-condition \"fix (X -> A) (\\ h x -> abs (rep (f h x))) == fix (X->A) f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-result-split" ((\ abs rep assC -> promoteDefR $ wwResultSplit (mkWWAssC assC) abs rep)
                                  :: CoreString -> CoreString -> RewriteH LCore -> RewriteH LCore)
                [ "Worker/Wrapper Split (Result Variant)",
                  "For any \"prog :: X -> A\", and given \"abs :: B -> A\" and \"rep :: A -> B\" as arguments,",
                  "and a proof of Assumption C (fix (X->A) (\\ h x -> abs (rep (f h x))) ==> fix (X->A) f), then",
                  "prog = expr  ==>  prog = let f = \\ prog -> expr",
                  "                          in let work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)",
                  "                              in \\ x0 -> abs (work x0)"
                ] .+ Introduce .+ Context
         , external "ww-result-split-unsafe" ((\ abs rep -> promoteDefR $ wwResultSplit Nothing abs rep)
                                       :: CoreString -> CoreString -> RewriteH LCore)
                [ "Unsafe Worker/Wrapper Split (Result Variant)",
                  "For any \"prog :: X -> A\", and given \"abs :: B -> A\" and \"rep :: A -> B\" as arguments, then",
                  "prog = expr  ==>  prog = let f = \\ prog -> expr",
                  "                          in let work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)",
                  "                              in \\ x0 -> abs (work x0)",
                  "Note: the pre-condition \"fix (X->A) (\\ h x -> abs (rep (f h x))) == fix (X->A) f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition .+ Unsafe
         , external "ww-result-split-static-arg" ((\ n is abs rep assC -> promoteDefR $ wwResultSplitStaticArg n is (mkWWAssC assC) abs rep)
                                      :: Int -> [Int] -> CoreString -> CoreString -> RewriteH LCore -> RewriteH LCore)
                [ "Worker/Wrapper Split - Static Argument Variant (Result Variant)",
                  "Perform the static argument transformation on the first n arguments, then perform the worker/wrapper split,",
                  "applying the given abs and rep functions to the specified (by index) static arguments before use."
                ] .+ Introduce .+ Context
         , external "ww-result-split-static-arg-unsafe" ((\ n is abs rep -> promoteDefR $ wwResultSplitStaticArg n is Nothing abs rep)
                                      :: Int -> [Int] -> CoreString -> CoreString -> RewriteH LCore)
                [ "Unsafe Worker/Wrapper Split - Static Argument Variant (Result Variant)",
                  "Perform the static argument transformation on the first n arguments, then perform the (unsafe) worker/wrapper split,",
                  "applying the given abs and rep functions to the specified (by index) static arguments before use."
                ] .+ Introduce .+ Context .+ PreCondition .+ Unsafe
         , external "ww-result-assumption-A" ((\ abs rep assA -> promoteExprBiR $ wwA (Just $ extractR assA) abs rep)
                                       :: CoreString -> CoreString -> RewriteH LCore -> BiRewriteH LCore)
                [ "Worker/Wrapper Assumption A (Result Variant)",
                  "For a \"abs :: B -> A\" and a \"rep :: A -> B\",",
                  "and given a proof of \"abs (rep a)  ==>  a\", then",
                  "abs (rep a)  <==>  a"
                ] .+ Introduce .+ Context
         , external "ww-result-assumption-B" ((\ abs rep f assB -> promoteExprBiR $ wwB (Just $ extractR assB) abs rep f)
                                       :: CoreString -> CoreString -> CoreString -> RewriteH LCore -> BiRewriteH LCore)
                [ "Worker/Wrapper Assumption B (Result Variant)",
                  "For a \"abs :: B -> A\", an \"rep :: A -> B\", and an \"f :: (X -> A) -> X -> A\",",
                  "and given a proof of \"abs (rep (f h x))  ==>  f h x\", then",
                  "abs (rep (f h x))  <==>  f h x"
                ] .+ Introduce .+ Context
         , external "ww-result-assumption-C" ((\ abs rep f assC -> promoteExprBiR $ wwC (Just $ extractR assC) abs rep f)
                                       :: CoreString -> CoreString -> CoreString -> RewriteH LCore -> BiRewriteH LCore)
                [ "Worker/Wrapper Assumption C (Result Variant)",
                  "For a \"abs :: B -> A\", an \"rep :: A -> B\", and an \"f :: (X -> A) -> X -> A\",",
                  "and given a proof of \"fix (X->A) (\\ h x -> abs (rep (f h x))) ==> fix (X->A) f\", then",
                  "fix (X->A) (\\ h x -> abs (rep (f h x)))  <==>  fix (X->A) f"
                ] .+ Introduce .+ Context
         , external "ww-result-assumption-A-unsafe" ((\ abs rep -> promoteExprBiR $ wwA Nothing abs rep)
                                              :: CoreString -> CoreString -> BiRewriteH LCore)
                [ "Unsafe Worker/Wrapper Assumption A (Result Variant)",
                  "For a \"abs :: B -> A\" and a \"rep :: A -> B\", then",
                  "abs (rep a)  <==>  a",
                  "Note: only use this if it's true!"
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-result-assumption-B-unsafe" ((\ abs rep f -> promoteExprBiR $ wwB Nothing abs rep f)
                                              :: CoreString -> CoreString -> CoreString -> BiRewriteH LCore)
                [ "Unsafe Worker/Wrapper Assumption B (Result Variant)",
                  "For a \"abs :: B -> A\", an \"rep :: A -> B\", and an \"f :: (X -> A) -> X -> A\", then",
                  "abs (rep (f h x))  <==>  f h x",
                  "Note: only use this if it's true!"
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-result-assumption-C-unsafe" ((\ abs rep f -> promoteExprBiR $ wwC Nothing abs rep f)
                                              :: CoreString -> CoreString -> CoreString -> BiRewriteH LCore)
                [ "Unsafe Worker/Wrapper Assumption C (Result Variant)",
                  "For a \"abs :: B -> A\", an \"rep :: A -> B\", and an \"f :: (X -> A) -> X -> A\", then",
                  "fix (X->A) (\\ h x -> abs (rep (f h x)))  <==>  fix (X->A) f",
                  "Note: only use this if it's true!"
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-result-AssA-to-AssB" (promoteExprR . wwResultAssAimpliesAssB . extractR :: RewriteH LCore -> RewriteH LCore)
                   [ "Convert a proof of worker/wrapper Assumption A into a proof of worker/wrapper Assumption B."
                   ]
         , external "ww-result-AssB-to-AssC" (promoteExprR . wwResultAssBimpliesAssC . extractR :: RewriteH LCore -> RewriteH LCore)
                   [ "Convert a proof of worker/wrapper Assumption B into a proof of worker/wrapper Assumption C."
                   ]
         , external "ww-result-AssA-to-AssC" (promoteExprR . wwResultAssAimpliesAssC . extractR :: RewriteH LCore -> RewriteH LCore)
                   [ "Convert a proof of worker/wrapper Assumption A into a proof of worker/wrapper Assumption C."
                   ]
         , external "ww-result-generate-fusion" (wwResultGenerateFusionT . mkWWAssC :: RewriteH LCore -> TransformH LCore ())
                   [ "Given a proof of Assumption C (fix (X->A) (\\ h x -> abs (rep (f h x))) ==> fix (X->A) f), then",
                     "execute this command on \"work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)\" to enable the \"ww-result-fusion\" rule thereafter.",
                     "Note that this is performed automatically as part of \"ww-result-split\"."
                   ] .+ Experiment .+ TODO
         , external "ww-result-generate-fusion-unsafe" (wwResultGenerateFusionT Nothing :: TransformH LCore ())
                   [ "Execute this command on \"work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)\" to enable the \"ww-fusion\" rule thereafter.",
                     "The precondition \"fix (X->A) (\\ h x -> abs (rep (f h x))) == fix (X->A) f\" is expected to hold.",
                     "Note that this is performed automatically as part of \"ww-result-split\"."
                   ] .+ Experiment .+ TODO
         , external "ww-result-fusion" (promoteExprBiR wwFusion :: BiRewriteH LCore)
                [ "Worker/Wrapper Fusion (Result Variant)",
                  "rep (abs (work x))  <==>  work x",
                  "Note: you are required to have previously executed the command \"ww-generate-fusion\" on the definition",
                  "      work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)"
                ] .+ Introduce .+ Context .+ PreCondition .+ TODO
         ]
  where
    mkWWAssC :: RewriteH LCore -> Maybe WWAssumption
    mkWWAssC r = Just (WWAssumption C (extractR r))

--------------------------------------------------------------------------------------------------


-- | For any @f :: (X -> A) -> (X -> A)@, and given @abs :: B -> A@ and @rep :: A -> B@ as arguments, then
--   @fix A f@  \<==\>  @\\ x1 -> abs (fix (X->B) (\\ h x2 -> rep (f (\\ x3 -> abs (h x3)) x2)) x1)@
wwResultFacBR :: Maybe WWAssumption -> CoreExpr -> CoreExpr -> BiRewriteH CoreExpr
wwResultFacBR mAss abs rep = beforeBiR (absRepTypes abs rep)
                                  (\ (tyA,tyB) -> bidirectional (wwL tyA tyB) wwR)
  where
    wwL :: Type -> Type -> RewriteH CoreExpr
    wwL tyA tyB = prefixFailMsg "worker/wrapper factorisation failed: " $
                  do (tyXA,f)  <- isFixExprT
                     (_,tyX,tA)  <- constT (splitFunTypeM tyXA)
#if __GLASGOW_HASKELL__ > 710
                     -- let tyXB  =  ForAllTy (Anon tyX) tyB
                     let tyXB  =  FunTy tyX tyB -- TODO: Does this work?
#else
                     let tyXB  =  FunTy tyX tyB
#endif
                     h         <- constT (newIdH "h" tyXB)
                     guardMsg (eqType tyA tA) ("abs/rep types do not match fix body type.")
                     x0        <- constT (newIdH "x0" tyX)
                     x1        <- constT (newIdH "x1" tyX)
                     x2        <- constT (newIdH "x2" tyX)

                     whenJust (verifyWWAss abs rep f) mAss

                     work <- buildFixT (Lam h (Lam x1 (App rep
                                                        (App (App f (Lam x2 (App abs (App (Var h) (Var x2)))))
                                                             (Var x1)
                                                        )
                                                   )))
                     return (Lam x0 (App abs (App work (Var x0))))

    wwR :: RewriteH CoreExpr
    wwR  =    prefixFailMsg "(reverse) worker/wrapper factorisation failed: " $
              withPatFailExc (strategyFailure wrongForm) $
              do Lam x0 (App abs2 (App fx (Var x0'))) <- idR
                 guardMsg (x0 == x0') wrongForm
                 (_, Lam h (Lam x1 (App rep1
                                        (App (App f (Lam x2 (App abs1 (App (Var h') (Var x2')))))
                                             (Var x1')
                                        )
                                  ))) <- isFixExprT <<< constant fx
                 guardMsg (x1 == x1' && x2 == x2' && h == h') wrongForm
                 guardMsg (equivalentBy exprAlphaEq [abs, abs1, abs2]) "abs's do not match."
                 guardMsg (exprAlphaEq rep rep1) "rep's do not match."
                 whenJust (verifyWWAss abs rep f) mAss
                 buildFixT f

    wrongForm :: String
    wrongForm = wrongExprForm "\\ x1 -> abs (fix (\\ h x2 -> rep (f (\\ x3 -> abs (h x3)) x2)) x1)"

-- | For any @f :: (X -> A) -> (X -> A)@, and given @abs :: B -> A@ and @rep :: A -> B@ as arguments, then
--   @fix A f@  \<==\>  @\\ x1 -> abs (fix (X->B) (\\ h x2 -> rep (f (\\ x3 -> abs (h x3)) x2)) x1)@
wwFac :: Maybe WWAssumption -> CoreString -> CoreString -> BiRewriteH CoreExpr
wwFac mAss = parse2beforeBiR (wwResultFacBR mAss)

--------------------------------------------------------------------------------------------------

-- | Given @abs :: B -> A@, @rep :: A -> B@ and @work :: X -> B@ as arguments, then
--   @rep (abs (work x))@  \<==\>  @work x@
wwResultFusionBR :: BiRewriteH CoreExpr
wwResultFusionBR =
    beforeBiR (prefixFailMsg "worker/wrapper fusion failed: " $
               withPatFailExc (strategyFailure "malformed WW Fusion rule.") $
               do Equiv w
                        (Lam x1 (App rep
                                     (App (App _ (Lam x2 (App abs (App w' (Var x2')))))
                                          (Var x1')
                                     )
                                )
                        ) <- constT (lemmaC <$> findLemma workLabel)
                  guardMsg (exprSyntaxEq w w' && x1 == x1' && x2 == x2') "malformed WW Fusion rule."
                  return (abs,rep,w)
              )
              (\ (abs,rep,work) -> bidirectional (fusL abs rep work) (fusR abs rep work))
  where
    fusL :: CoreExpr -> CoreExpr -> CoreExpr -> RewriteH CoreExpr
    fusL abs rep work =
           prefixFailMsg "worker/wrapper fusion failed: " $
           withPatFailExc (strategyFailure (wrongExprForm "rep (abs (work x))")) $
           do App rep' (App abs' (App work' x)) <- idR
              guardMsg (exprAlphaEq abs abs') "abs does not match."
              guardMsg (exprAlphaEq rep rep') "rep does not match."
              guardMsg (exprAlphaEq work work') "worker does not match."
              return $ App work x

    fusR :: CoreExpr -> CoreExpr -> CoreExpr -> RewriteH CoreExpr
    fusR abs rep work =
           prefixFailMsg "(reverse) worker/wrapper fusion failed: " $
           withPatFailExc (strategyFailure (wrongExprForm "work x")) $
           do App work' x <- idR
              guardMsg (exprAlphaEq work work') "worker does not match."
              return $ App rep (App abs (App work x))

-- | Given @abs :: B -> A@, @rep :: A -> B@ and @work :: X -> B@ as arguments, then
--   @rep (abs (work x))@  \<==\>  @work x@
wwFusion :: BiRewriteH CoreExpr
wwFusion = wwResultFusionBR

--------------------------------------------------------------------------------------------------

-- | Save the recursive definition of work in the stash, so that we can later verify uses of 'wwResultFusionBR'.
--   Must be applied to a definition of the form: @work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)@
--   Note that this is performed automatically as part of 'wwResultSplitR'.
wwResultGenerateFusionT :: Maybe WWAssumption -> TransformH LCore ()
wwResultGenerateFusionT mAss =
    prefixFailMsg "generate WW fusion failed: " $
    withPatFailExc (strategyFailure wrongForm) $
    do Def w e@(Lam x1 (App rep
                          (App (App f (Lam x2 (App abs (App (Var w') (Var x2')))))
                               (Var x1')
                          )
                       )
               ) <- projectT
       guardMsg (w == w' && x1 == x1' && x2 == x2') wrongForm
       whenJust (verifyWWAss abs rep f) mAss
       insertLemmaT workLabel $ Lemma (Equiv (varToCoreExpr w) e) Proven NotUsed
  where
    wrongForm = "definition does not have the form: work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)"


--------------------------------------------------------------------------------------------------

-- | \\ abs rep -> (@prog = expr@  ==>  @prog = let f = \\ prog -> expr in let work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1) in \\ x0 -> abs (work x0)@)
wwResultSplitR :: Maybe WWAssumption -> CoreExpr -> CoreExpr -> RewriteH CoreDef
wwResultSplitR mAss abs rep =
      fixIntroRecR
      >>> defAllR idR ( appAllR idR (letIntroR "f")
                        >>> letFloatArgR
                        >>> letAllR idR ( forwardT (wwResultFacBR mAss abs rep)
                                          >>> lamAllR idR (appAllR idR (appAllR ( unfoldNameR (fromString "Data.Function.fix")
                                                                                  >>> alphaLetWithR ["work"]
                                                                                  >>> letRecAllR (\ _ -> defAllR idR (betaReduceR >>> letNonRecSubstR)
                                                                                                         >>> (extractT (wwResultGenerateFusionT mAss) >> idR)
                                                                                                 )
                                                                                                 idR
                                                                                )
                                                                                idR
                                                                        >>> letFloatAppR
                                                                       )
                                                           >>> letFloatArgR
                                                          )
                                          >>> letFloatLamR
                                        )
                      )

-- | \\ abs rep -> (@prog = expr@  ==>  @prog = let f = \\ prog -> expr in let work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1) in \\ x0 -> abs (work x0))@
wwResultSplit :: Maybe WWAssumption -> CoreString -> CoreString -> RewriteH CoreDef
wwResultSplit mAss absS repS = (parseCoreExprT absS &&& parseCoreExprT repS) >>= uncurry (wwResultSplitR mAss)

-- | As 'wwResultSplit' but performs the static-argument transformation for @n@ static arguments first, and optionally provides some of those arguments (specified by index) to all calls of abs and rep.
--   This is useful if, for example, the expression, and abs and rep, all have a @forall@ type.
wwResultSplitStaticArg :: Int -> [Int] -> Maybe WWAssumption -> CoreString -> CoreString -> RewriteH CoreDef
wwResultSplitStaticArg 0 _  = wwResultSplit
wwResultSplitStaticArg n is = \ mAss absS repS ->
                            prefixFailMsg "worker/wrapper split (static argument variant) failed: " $
                            do guardMsg (all (< n) is) "arguments for abs and rep must be chosen from the statically transformed arguments."
                               bs <- defT successT (arr collectBinders) (\ () -> take n . fst)
                               let args = varsToCoreExprs [ b | (i,b) <- zip [0..] bs, i `elem` is ]

                               staticArgPosR [0..(n-1)] >>> defAllR idR
                                                                    (let wwSplitArgsR :: RewriteH CoreDef
                                                                         wwSplitArgsR = do abs  <- parseCoreExprT absS
                                                                                           rep  <- parseCoreExprT repS
                                                                                           wwResultSplitR mAss (mkCoreApps abs args) (mkCoreApps rep args)
                                                                      in
                                                                         extractR $ do p <- considerConstructT LetExpr
                                                                                       localPathR p $ promoteExprR (letRecAllR (const wwSplitArgsR) idR >>> letSubstR)
                                                                    )

--------------------------------------------------------------------------------------------------

-- | Convert a proof of WW Assumption A into a proof of WW Assumption B.
wwResultAssAimpliesAssB :: RewriteH CoreExpr -> RewriteH CoreExpr
wwResultAssAimpliesAssB = id

-- | Convert a proof of WW Assumption B into a proof of WW Assumption C.
wwResultAssBimpliesAssC :: RewriteH CoreExpr -> RewriteH CoreExpr
wwResultAssBimpliesAssC assB = appAllR idR (lamAllR idR (lamAllR idR assB >>> etaReduceR) >>> etaReduceR)

-- | Convert a proof of WW Assumption A into a proof of WW Assumption C.
wwResultAssAimpliesAssC :: RewriteH CoreExpr -> RewriteH CoreExpr
wwResultAssAimpliesAssC =  wwResultAssBimpliesAssC . wwResultAssAimpliesAssB

--------------------------------------------------------------------------------------------------

-- | @abs (rep a)@  \<==\>  @a@
wwResultAssA :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption A
       -> CoreExpr                  -- ^ abs
       -> CoreExpr                  -- ^ rep
       -> BiRewriteH CoreExpr
wwResultAssA mr abs rep = beforeBiR
                      (do whenJust (verifyAssA abs rep) mr
                          absRepTypes abs rep
                      )
                      (\ (tyA,_) -> bidirectional wwAL (wwAR tyA))
  where
    wwAL :: RewriteH CoreExpr
    wwAL = withPatFailExc (strategyFailure (wrongExprForm "abs (rep a)")) $
           do App abs' (App rep' a) <- idR
              guardMsg (exprAlphaEq abs abs') "given wrapper does not match wrapper in expression."
              guardMsg (exprAlphaEq rep rep') "given unwrapper does not match unwrapper in expression."
              return a

    wwAR :: Type -> RewriteH CoreExpr
    wwAR tyA = do a <- idR
                  guardMsg (exprKindOrType a `eqType` tyA) "type of expression does not match types of abs/rep."
                  return $ App abs (App rep a)

-- | @abs (rep a)@  \<==\>  @a@
wwA :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption A
    -> CoreString                -- ^ abs
    -> CoreString                -- ^ rep
    -> BiRewriteH CoreExpr
wwA mr = parse2beforeBiR (wwResultAssA mr)

-- | @abs (rep (f h x))@  \<==\>  @f h x@
wwResultAssB :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption B
       -> CoreExpr                  -- ^ abs
       -> CoreExpr                  -- ^ rep
       -> CoreExpr                  -- ^ f
       -> BiRewriteH CoreExpr
wwResultAssB mr abs rep f = beforeBiR (whenJust (verifyAssB abs rep f) mr)
                                (\ () -> bidirectional wwBL wwBR)
  where
    assA :: BiRewriteH CoreExpr
    assA = wwResultAssA Nothing abs rep

    wwBL :: RewriteH CoreExpr
    wwBL = withPatFailExc (strategyFailure (wrongExprForm "abs (rep (f h x))")) $
           do App _ (App _ (App (App f' _) _)) <- idR
              guardMsg (exprAlphaEq f f') "given body function does not match expression."
              forwardT assA

    wwBR :: RewriteH CoreExpr
    wwBR = withPatFailExc (strategyFailure (wrongExprForm "f h x")) $
           do App (App f' _) _ <- idR
              guardMsg (exprAlphaEq f f') "given body function does not match expression."
              backwardT assA

-- | @abs (rep (f h x))@  \<==\>  @f h x@
wwB :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption B
    -> CoreString                -- ^ abs
    -> CoreString                -- ^ rep
    -> CoreString                -- ^ f
    -> BiRewriteH CoreExpr
wwB mr = parse3beforeBiR (wwResultAssB mr)

-- | @fix (X->A) (\ h x -> abs (rep (f h x)))@  \<==\>  @fix (X->A) f@
wwResultAssC :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption C
       -> CoreExpr                  -- ^ abs
       -> CoreExpr                  -- ^ rep
       -> CoreExpr                  -- ^ f
       -> BiRewriteH CoreExpr
wwResultAssC mr abs rep f = beforeBiR (do _ <- isFixExprT
                                          whenJust (verifyAssC abs rep f) mr
                                      )
                                      (\ () -> bidirectional wwCL wwCR)
  where
    assB :: BiRewriteH CoreExpr
    assB = wwResultAssB Nothing abs rep f

    wwCL :: RewriteH CoreExpr
    wwCL = wwResultAssAimpliesAssC (forwardT assB)

    wwCR :: RewriteH CoreExpr
    wwCR = appAllR idR (etaExpandR "h" >>> lamAllR idR (etaExpandR "x" >>> lamAllR idR (backwardT assB)))

-- | @fix (X->A) (\ h x -> abs (rep (f h x)))@  \<==\>  @fix (X->A) f@
wwC :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption C
    -> CoreString                -- ^ abs
    -> CoreString                -- ^ rep
    -> CoreString                -- ^ f
    -> BiRewriteH CoreExpr
wwC mr = parse3beforeBiR (wwResultAssC mr)

--------------------------------------------------------------------------------------------------

verifyWWAss :: CoreExpr        -- ^ abs
            -> CoreExpr        -- ^ rep
            -> CoreExpr        -- ^ f
            -> WWAssumption
            -> TransformH x ()
verifyWWAss abs rep f (WWAssumption tag ass) =
    case tag of
      A -> verifyAssA abs rep ass
      B -> verifyAssB abs rep f ass
      C -> verifyAssC abs rep f ass

verifyAssA :: CoreExpr          -- ^ abs
           -> CoreExpr          -- ^ rep
           -> RewriteH CoreExpr -- ^ WW Assumption A
           -> TransformH x ()
verifyAssA abs rep assA =
  prefixFailMsg ("verification of worker/wrapper Assumption A failed: ") $
  do _ <- absRepTypes abs rep  -- this check is redundant, but will produce a better error message
     verifyRetractionT abs rep assA

verifyAssB :: CoreExpr          -- ^ abs
           -> CoreExpr          -- ^ rep
           -> CoreExpr          -- ^ f
           -> RewriteH CoreExpr -- ^ WW Assumption B
           -> TransformH x ()
verifyAssB abs rep f assB =
  prefixFailMsg ("verification of worker/wrapper assumption B failed: ") $
  do (tyA,_)    <- absRepTypes abs rep
     (_,tyXA)   <- constT (endoFunExprTypeM f)
     (_,tyX,tA) <- constT (splitFunTypeM tyXA)
     guardMsg (eqType tyA tA) "type of program body does not match types of abs/rep."
     h        <- constT (newIdH "h" tyXA)
     x        <- constT (newIdH "x" tyX)
     let lhs = App abs (App rep (App (App f (Var h)) (Var x)))
         rhs = App (App f (Var h)) (Var x)
     verifyEqualityLeftToRightT lhs rhs assB

verifyAssC :: CoreExpr          -- ^ abs
           -> CoreExpr          -- ^ rep
           -> CoreExpr          -- ^ f
           -> RewriteH CoreExpr -- ^ WW Assumption C
           -> TransformH a ()
verifyAssC abs rep f assC =
  prefixFailMsg ("verification of worker/wrapper assumption C failed: ") $
  do (tyA,_)    <- absRepTypes abs rep
     (_,tyXA)   <- constT (endoFunExprTypeM f)
     (_,tyX,tA) <- constT (splitFunTypeM tyXA)
     guardMsg (eqType tyA tA) "type of program body does not match types of abs/rep."
     h        <- constT (newIdH "h" tyXA)
     x        <- constT (newIdH "x" tyX)
     rhs      <- buildFixT f
     lhs      <- buildFixT (Lam h (Lam x (App abs (App rep (App (App f (Var h)) (Var x))))))
     verifyEqualityLeftToRightT lhs rhs assC

--------------------------------------------------------------------------------------------------

absRepTypes :: MonadCatch m => CoreExpr -> CoreExpr -> m (Type,Type)
absRepTypes abs rep = setFailMsg "given expressions have the wrong types to form a valid abs/rep pair." $
                      funExprsWithInverseTypes rep abs

--------------------------------------------------------------------------------------------------
