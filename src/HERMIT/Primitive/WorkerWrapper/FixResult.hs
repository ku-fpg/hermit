{-# LANGUAGE TupleSections #-}

module HERMIT.Primitive.WorkerWrapper.FixResult
       ( -- * The Worker/Wrapper Transformation (Result Variant)
         -- | Note that many of these operations require 'Data.Function.fix' to be in scope.
         HERMIT.Primitive.WorkerWrapper.FixResult.externals
       , workerWrapperFacBR
       , workerWrapperSplitR
       , workerWrapperSplitParam
       , workerWrapperGenerateFusionR
       , workerWrapperFusionBR
       , wwAssA
       , wwAssB
       , wwAssC
       )
where

import Prelude hiding (abs)

import Control.Arrow

import HERMIT.Core
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC
import HERMIT.Utilities

import HERMIT.Primitive.AlphaConversion
import HERMIT.Primitive.Common
import HERMIT.Primitive.Function
import HERMIT.Primitive.Local
import HERMIT.Primitive.Navigation
import HERMIT.Primitive.New -- TODO: Sort out heirarchy
import HERMIT.Primitive.FixPoint
import HERMIT.Primitive.Unfold

import HERMIT.Primitive.WorkerWrapper.Common

import qualified Language.Haskell.TH as TH

--------------------------------------------------------------------------------------------------

-- | Externals for manipulating fixed points, and for the worker/wrapper transformation.
externals ::  [External]
externals =
         [
           external "ww-result-factorisation" ((\ abs rep assC -> promoteExprBiR $ workerWrapperFac (mkWWAssC assC) abs rep)
                                          :: CoreString -> CoreString -> RewriteH Core -> BiRewriteH Core)
                [ "Worker/Wrapper Factorisation (Result Variant)",
                  "For any \"f :: (X -> A) -> (X -> A)\", and given \"abs :: B -> A\" and \"rep :: A -> B\" as arguments,",
                  "and a proof of Assumption C (fix (X -> A) (\\ h x -> abs (rep (f h x))) ==> fix (X->A) f), then",
                  "fix (X->A) f  ==>  \\ x1 -> abs (fix (X->B) (\\ h x2 -> rep (f (\\ x3 -> abs (h x3)) x2)) x1"
                ] .+ Introduce .+ Context
         , external "ww-result-factorisation-unsafe" ((\ abs rep -> promoteExprBiR $ workerWrapperFac Nothing abs rep)
                                               :: CoreString -> CoreString -> BiRewriteH Core)
                [ "Unsafe Worker/Wrapper Factorisation (Result Variant)",
                  "For any \"f :: (X -> A) -> (X -> A)\", and given \"abs :: B -> A\" and \"rep :: A -> B\" as arguments, then",
                  "fix (X->A) f  ==>  \\ x1 -> abs (fix (X->B) (\\ h x2 -> rep (f (\\ x3 -> abs (h x3)) x2)) x1",
                  "Note: the pre-condition \"fix (X -> A) (\\ h x -> abs (rep (f h x))) == fix (X->A) f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-result-split" ((\ abs rep assC -> promoteDefR $ workerWrapperSplit (mkWWAssC assC) abs rep)
                                  :: CoreString -> CoreString -> RewriteH Core -> RewriteH Core)
                [ "Worker/Wrapper Split (Result Variant)",
                  "For any \"prog :: X -> A\", and given \"abs :: B -> A\" and \"rep :: A -> B\" as arguments,",
                  "and a proof of Assumption C (fix (X->A) (\\ h x -> abs (rep (f h x))) ==> fix (X->A) f), then",
                  "prog = expr  ==>  prog = let f = \\ prog -> expr",
                  "                          in let work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)",
                  "                              in \\ x0 -> abs (work x0)"
                ] .+ Introduce .+ Context
         , external "ww-result-split-unsafe" ((\ abs rep -> promoteDefR $ workerWrapperSplit Nothing abs rep)
                                       :: CoreString -> CoreString -> RewriteH Core)
                [ "Unsafe Worker/Wrapper Split (Result Variant)",
                  "For any \"prog :: X -> A\", and given \"abs :: B -> A\" and \"rep :: A -> B\" as arguments, then",
                  "prog = expr  ==>  prog = let f = \\ prog -> expr",
                  "                          in let work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)",
                  "                              in \\ x0 -> abs (work x0)",
                  "Note: the pre-condition \"fix (X->A) (\\ h x -> abs (rep (f h x))) == fix (X->A) f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-result-split-param" ((\ n abs rep assC -> promoteDefR $ workerWrapperSplitParam n (mkWWAssC assC) abs rep)
                                      :: Int -> CoreString -> CoreString -> RewriteH Core -> RewriteH Core)
                [ "Worker/Wrapper Split - Type Paramater Variant (Result Variant)",
                  "For any \"prog :: forall t1 t2 .. tn . X -> A\",",
                  "and given \"abs :: forall t1 t2 .. tn . B -> A\" and \"rep :: forall t1 t2 .. tn . A -> B\" as arguments,",
                  "and a proof of Assumption C (forall t1 t2 .. tn . fix (X->A) (\\ h x -> abs t1 t2 .. tn (rep t1 t2 .. tn (f h x))) ==> fix (X->A) f), then",
                  "prog = expr  ==>  prog = \\ t1 t2 .. tn -> let f = \\ prog -> expr t1 t2 .. tn",
                  "                                            in let work = \\ x1 -> rep t1 t2 .. tn (f (\\ x2 -> abs t1 t2 .. tn (work x2)) x1)",
                  "                                                in \\ x0 -> abs t1 t2 .. tn (work x0)"
                ] .+ Introduce .+ Context .+ PreCondition .+ TODO .+ Experiment
         , external "ww-result-split-param-unsafe" ((\ n abs rep -> promoteDefR $ workerWrapperSplitParam n Nothing abs rep)
                                             :: Int -> CoreString -> CoreString -> RewriteH Core)
                [ "Unsafe Worker/Wrapper Split - Type Paramater Variant",
                  "For any \"prog :: forall t1 t2 .. tn . X -> A\",",
                  "and given \"abs :: forall t1 t2 .. tn . B -> A\" and \"rep :: forall t1 t2 .. tn . A -> B\" as arguments, then",
                  "prog = expr  ==>  prog = \\ t1 t2 .. tn -> let f = \\ prog -> expr t1 t2 .. tn",
                  "                                            in let work = \\ x1 -> rep t1 t2 .. tn (f (\\ x2 -> abs t1 t2 .. tn (work x2)) x1)",
                  "                                                in \\ x0 -> abs t1 t2 .. tn (work x0)",
                  "Note: the pre-condition \"forall t1 t2 .. tn . fix (X->A) (\\ h x -> abs t1 t2 .. tn (rep t1 t2 .. tn (f h x))) == fix (X->A) f\" is expected to hold."
                ] .+ Introduce .+ Context .+ PreCondition .+ TODO .+ Experiment
         , external "ww-result-assumption-A" ((\ abs rep assA -> promoteExprBiR $ wwA (Just $ extractR assA) abs rep)
                                       :: CoreString -> CoreString -> RewriteH Core -> BiRewriteH Core)
                [ "Worker/Wrapper Assumption A (Result Variant)",
                  "For a \"abs :: B -> A\" and a \"rep :: A -> B\",",
                  "and given a proof of \"abs (rep a)  ==>  a\", then",
                  "abs (rep a)  <==>  a"
                ] .+ Introduce .+ Context
         , external "ww-result-assumption-B" ((\ abs rep f assB -> promoteExprBiR $ wwB (Just $ extractR assB) abs rep f)
                                       :: CoreString -> CoreString -> CoreString -> RewriteH Core -> BiRewriteH Core)
                [ "Worker/Wrapper Assumption B (Result Variant)",
                  "For a \"abs :: B -> A\", an \"rep :: A -> B\", and an \"f :: (X -> A) -> X -> A\",",
                  "and given a proof of \"abs (rep (f h x))  ==>  f h x\", then",
                  "abs (rep (f h x))  <==>  f h x"
                ] .+ Introduce .+ Context
         , external "ww-result-assumption-C" ((\ abs rep f assC -> promoteExprBiR $ wwC (Just $ extractR assC) abs rep f)
                                       :: CoreString -> CoreString -> CoreString -> RewriteH Core -> BiRewriteH Core)
                [ "Worker/Wrapper Assumption C (Result Variant)",
                  "For a \"abs :: B -> A\", an \"rep :: A -> B\", and an \"f :: (X -> A) -> X -> A\",",
                  "and given a proof of \"fix (X->A) (\\ h x -> abs (rep (f h x))) ==> fix (X->A) f\", then",
                  "fix (X->A) (\\ h x -> abs (rep (f h x)))  <==>  fix (X->A) f"
                ] .+ Introduce .+ Context
         , external "ww-result-assumption-A-unsafe" ((\ abs rep -> promoteExprBiR $ wwA Nothing abs rep)
                                              :: CoreString -> CoreString -> BiRewriteH Core)
                [ "Unsafe Worker/Wrapper Assumption A (Result Variant)",
                  "For a \"abs :: B -> A\" and a \"rep :: A -> B\", then",
                  "abs (rep a)  <==>  a",
                  "Note: only use this if it's true!"
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-result-assumption-B-unsafe" ((\ abs rep f -> promoteExprBiR $ wwB Nothing abs rep f)
                                              :: CoreString -> CoreString -> CoreString -> BiRewriteH Core)
                [ "Unsafe Worker/Wrapper Assumption B (Result Variant)",
                  "For a \"abs :: B -> A\", an \"rep :: A -> B\", and an \"f :: (X -> A) -> X -> A\", then",
                  "abs (rep (f h x))  <==>  f h x",
                  "Note: only use this if it's true!"
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-result-assumption-C-unsafe" ((\ abs rep f -> promoteExprBiR $ wwC Nothing abs rep f)
                                              :: CoreString -> CoreString -> CoreString -> BiRewriteH Core)
                [ "Unsafe Worker/Wrapper Assumption C (Result Variant)",
                  "For a \"abs :: B -> A\", an \"rep :: A -> B\", and an \"f :: (X -> A) -> X -> A\", then",
                  "fix (X->A) (\\ h x -> abs (rep (f h x)))  <==>  fix (X->A) f",
                  "Note: only use this if it's true!"
                ] .+ Introduce .+ Context .+ PreCondition
         , external "ww-result-AssA-to-AssB" (promoteExprR . wwAssAimpliesAssB . extractR :: RewriteH Core -> RewriteH Core)
                   [ "Convert a proof of worker/wrapper Assumption A into a proof of worker/wrapper Assumption B."
                   ]
         , external "ww-result-AssB-to-AssC" (promoteExprR . wwAssBimpliesAssC . extractR :: RewriteH Core -> RewriteH Core)
                   [ "Convert a proof of worker/wrapper Assumption B into a proof of worker/wrapper Assumption C."
                   ]
         , external "ww-result-AssA-to-AssC" (promoteExprR . wwAssAimpliesAssC . extractR :: RewriteH Core -> RewriteH Core)
                   [ "Convert a proof of worker/wrapper Assumption A into a proof of worker/wrapper Assumption C."
                   ]
         , external "ww-result-generate-fusion" (workerWrapperGenerateFusionR . mkWWAssC :: RewriteH Core -> RewriteH Core)
                   [ "Given a proof of Assumption C (fix (X->A) (\\ h x -> abs (rep (f h x))) ==> fix (X->A) f), then",
                     "execute this command on \"work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)\" to enable the \"ww-result-fusion\" rule thereafter.",
                     "Note that this is performed automatically as part of \"ww-result-split\"."
                   ] .+ Experiment .+ TODO
         , external "ww-result-generate-fusion-unsafe" (workerWrapperGenerateFusionR Nothing :: RewriteH Core)
                   [ "Execute this command on \"work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)\" to enable the \"ww-fusion\" rule thereafter.",
                     "The precondition \"fix (X->A) (\\ h x -> abs (rep (f h x))) == fix (X->A) f\" is expected to hold.",
                     "Note that this is performed automatically as part of \"ww-result-split\"."
                   ] .+ Experiment .+ TODO
         , external "ww-result-fusion" (promoteExprBiR workerWrapperFusion :: BiRewriteH Core)
                [ "Worker/Wrapper Fusion (Result Variant)",
                  "rep (abs (work x))  <==>  work x",
                  "Note: you are required to have previously executed the command \"ww-generate-fusion\" on the definition",
                  "      work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)"
                ] .+ Introduce .+ Context .+ PreCondition .+ TODO
         ]
  where
    mkWWAssC :: RewriteH Core -> Maybe WWAssumption
    mkWWAssC r = Just (WWAssumption C (extractR r))

--------------------------------------------------------------------------------------------------


-- | For any @f :: (X -> A) -> (X -> A)@, and given @abs :: B -> A@ and @rep :: A -> B@ as arguments, then
--   @fix A f@  \<==\>  @\\ x1 -> abs (fix (X->B) (\\ h x2 -> rep (f (\\ x3 -> abs (h x3)) x2)) x1)@
workerWrapperFacBR :: Maybe WWAssumption -> CoreExpr -> CoreExpr -> BiRewriteH CoreExpr
workerWrapperFacBR mAss abs rep = beforeBiR (absRepTypes abs rep)
                                  (\ (tyA,tyB) -> bidirectional (wwL tyA tyB) wwR)
  where
    wwL :: Type -> Type -> RewriteH CoreExpr
    wwL tyA tyB = prefixFailMsg "worker/wrapper factorisation failed: " $
                  do (tyXA,f)  <- isFixExpr
                     (tyX,tA)  <- constT (splitFunTypeM tyXA)
                     let tyXB  =  FunTy tyX tyB
                     h         <- constT (newIdH "h" tyXB)
                     guardMsg (eqType tyA tA) ("abs/rep types do not match fix body type.")
                     x0        <- constT (newIdH "x0" tyX)
                     x1        <- constT (newIdH "x1" tyX)
                     x2        <- constT (newIdH "x2" tyX)

                     whenJust (verifyWWAss abs rep f) mAss

                     work <- mkFix (Lam h (Lam x1 (App rep
                                                       (App (App f (Lam x2 (App abs (App (Var h) (Var x2)))))
                                                            (Var x1)
                                                       )
                                               )))
                     return (Lam x0 (App abs (App work (Var x0))))

    wwR :: RewriteH CoreExpr
    wwR  =    prefixFailMsg "(reverse) worker/wrapper factorisation failed: " $
              withPatFailMsg wrongForm $
              do Lam x0 (App abs2 (App fx (Var x0'))) <- idR
                 guardMsg (x0 == x0') wrongForm
                 (_, Lam h (Lam x1 (App rep1
                                        (App (App f (Lam x2 (App abs1 (App (Var h') (Var x2')))))
                                             (Var x1')
                                        )
                                  ))) <- isFixExpr <<< constant fx
                 guardMsg (x1 == x1' && x2 == x2' && h == h') wrongForm
                 guardMsg (equivalentBy exprAlphaEq [abs, abs1, abs2]) "abs's do not match."
                 guardMsg (exprAlphaEq rep rep1) "rep's do not match."
                 whenJust (verifyWWAss abs rep f) mAss
                 mkFix f

    wrongForm :: String
    wrongForm = wrongExprForm "\\ x1 -> abs (fix (\\ h x2 -> rep (f (\\ x3 -> abs (h x3)) x2)) x1)"

-- | For any @f :: (X -> A) -> (X -> A)@, and given @abs :: B -> A@ and @rep :: A -> B@ as arguments, then
--   @fix A f@  \<==\>  @\\ x1 -> abs (fix (X->B) (\\ h x2 -> rep (f (\\ x3 -> abs (h x3)) x2)) x1)@
workerWrapperFac :: Maybe WWAssumption -> CoreString -> CoreString -> BiRewriteH CoreExpr
workerWrapperFac mAss = parse2beforeBiR (workerWrapperFacBR mAss)

--------------------------------------------------------------------------------------------------

-- | Given @abs :: B -> A@, @rep :: A -> B@ and @work :: X -> B@ as arguments, then
--   @rep (abs (work x))@  \<==\>  @work x@
workerWrapperFusionBR :: BiRewriteH CoreExpr
workerWrapperFusionBR =
    beforeBiR (prefixFailMsg "worker/wrapper fusion failed: " $
               withPatFailMsg "malformed WW Fusion rule." $
               do Def w (Lam x1 (App rep
                                     (App (App _ (Lam x2 (App abs (App (Var w') (Var x2')))))
                                          (Var x1')
                                     )
                                )
                        ) <- constT (lookupDef workLabel)
                  guardMsg (w == w' && x1 == x1' && x2 == x2') "malformed WW Fusion rule."
                  return (abs,rep,Var w)
              )
              (\ (abs,rep,work) -> bidirectional (fusL abs rep work) (fusR abs rep work))
  where
    fusL :: CoreExpr -> CoreExpr -> CoreExpr -> RewriteH CoreExpr
    fusL abs rep work =
           prefixFailMsg "worker/wrapper fusion failed: " $
           withPatFailMsg (wrongExprForm "rep (abs (work x))") $
           do App rep' (App abs' (App work' x)) <- idR
              guardMsg (exprAlphaEq abs abs') "abs does not match."
              guardMsg (exprAlphaEq rep rep') "rep does not match."
              guardMsg (exprAlphaEq work work') "worker does not match."
              return $ App work x

    fusR :: CoreExpr -> CoreExpr -> CoreExpr -> RewriteH CoreExpr
    fusR abs rep work =
           prefixFailMsg "(reverse) worker/wrapper fusion failed: " $
           withPatFailMsg (wrongExprForm "work x") $
           do App work' x <- idR
              guardMsg (exprAlphaEq work work') "worker does not match."
              return $ App rep (App abs (App work x))

-- | Given @abs :: B -> A@, @rep :: A -> B@ and @work :: X -> B@ as arguments, then
--   @rep (abs (work x))@  \<==\>  @work x@
workerWrapperFusion :: BiRewriteH CoreExpr
workerWrapperFusion = workerWrapperFusionBR

--------------------------------------------------------------------------------------------------

-- | Save the recursive definition of work in the stash, so that we can later verify uses of 'workerWrapperFusionBR'.
--   Must be applied to a definition of the form: @work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)@
--   Note that this is performed automatically as part of 'workerWrapperSplitR'.
workerWrapperGenerateFusionR :: Maybe WWAssumption -> RewriteH Core
workerWrapperGenerateFusionR mAss =
    prefixFailMsg "generate WW fusion failed: " $
    withPatFailMsg wrongForm $
    do Def w (Lam x1 (App rep
                          (App (App f (Lam x2 (App abs (App (Var w') (Var x2')))))
                               (Var x1')
                          )
                     )
             ) <- projectT
       guardMsg (w == w' && x1 == x1' && x2 == x2') wrongForm
       whenJust (verifyWWAss abs rep f) mAss
       rememberR workLabel
  where
    wrongForm = "definition does not have the form: work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1)"


--------------------------------------------------------------------------------------------------

-- | \\ abs rep -> (@prog = expr@  ==>  @prog = let f = \\ prog -> expr in let work = \\ x1 -> rep (f (\\ x2 -> abs (work x2)) x1) in \\ x0 -> abs (work x0)@)
workerWrapperSplitR :: Maybe WWAssumption -> CoreExpr -> CoreExpr -> RewriteH CoreDef
workerWrapperSplitR mAss abs rep =
  let work = TH.mkName "work"
      fx   = TH.mkName "fix"
   in
      fixIntro
      >>> defAllR idR ( appAllR idR (letIntroR "f")
                        >>> letFloatArgR
                        >>> letAllR idR ( forewardT (workerWrapperFacBR mAss abs rep)
                                          >>> lamAllR idR (appAllR idR (appAllR ( unfoldNameR fx
                                                                                  >>> alphaLetWith [work]
                                                                                  >>> letRecAllR (\ _ -> defAllR idR (betaReduceR >>> letNonRecSubstR)
                                                                                                         >>> extractR (workerWrapperGenerateFusionR mAss)
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
workerWrapperSplit :: Maybe WWAssumption -> CoreString -> CoreString -> RewriteH CoreDef
workerWrapperSplit mAss absS repS = (parseCoreExprT absS &&& parseCoreExprT repS) >>= uncurry (workerWrapperSplitR mAss)

-- | As 'workerWrapperSplit' but performs the static-argument transformation for @n@ type paramaters first, providing these types as arguments to all calls of abs and rep.
--   This is useful if the expression, and abs and rep, all have a @forall@ type.
workerWrapperSplitParam :: Int -> Maybe WWAssumption -> CoreString -> CoreString -> RewriteH CoreDef
workerWrapperSplitParam 0 = workerWrapperSplit
workerWrapperSplitParam n = \ mAss absS repS ->
                            prefixFailMsg "worker/wrapper split (forall variant) failed: " $
                            do guardMsg (n == 1) "currently only supports 1 type paramater."
                               withPatFailMsg "right-hand-side of definition does not have the form: Lam t e" $
                                 do Def _ (Lam t _) <- idR
                                    guardMsg (isTyVar t) "first argument is not a type."
                                    let splitAtDefR :: RewriteH Core
                                        splitAtDefR = pathR [Let_Bind, Rec_Def 0] $ promoteR $
                                                        do abs  <- parseCoreExprT absS
                                                           rep  <- parseCoreExprT repS
                                                           let ty = Type (TyVarTy t)
                                                           workerWrapperSplitR mAss (App abs ty) (App rep ty)
                                    staticArgR >>> extractR (do p <- considerConstructT LetExpr
                                                                localPathR p (splitAtDefR >>> promoteExprR letSubstR)
                                                            )

--------------------------------------------------------------------------------------------------

-- | Convert a proof of WW Assumption A into a proof of WW Assumption B.
wwAssAimpliesAssB :: RewriteH CoreExpr -> RewriteH CoreExpr
wwAssAimpliesAssB = id

-- | Convert a proof of WW Assumption B into a proof of WW Assumption C.
wwAssBimpliesAssC :: RewriteH CoreExpr -> RewriteH CoreExpr
wwAssBimpliesAssC assB = appAllR idR (lamAllR idR (lamAllR idR assB >>> etaReduceR) >>> etaReduceR)

-- | Convert a proof of WW Assumption A into a proof of WW Assumption C.
wwAssAimpliesAssC :: RewriteH CoreExpr -> RewriteH CoreExpr
wwAssAimpliesAssC =  wwAssBimpliesAssC . wwAssAimpliesAssB

--------------------------------------------------------------------------------------------------

-- | @abs (rep a)@  \<==\>  @a@
wwAssA :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption A
       -> CoreExpr                  -- ^ abs
       -> CoreExpr                  -- ^ rep
       -> BiRewriteH CoreExpr
wwAssA mr abs rep = beforeBiR
                      (do whenJust (verifyAssA abs rep) mr
                          absRepTypes abs rep
                      )
                      (\ (tyA,_) -> bidirectional wwAL (wwAR tyA))
  where
    wwAL :: RewriteH CoreExpr
    wwAL = withPatFailMsg (wrongExprForm "abs (rep a)") $
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
wwA mr = parse2beforeBiR (wwAssA mr)

-- | @abs (rep (f h x))@  \<==\>  @f h x@
wwAssB :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption B
       -> CoreExpr                  -- ^ abs
       -> CoreExpr                  -- ^ rep
       -> CoreExpr                  -- ^ f
       -> BiRewriteH CoreExpr
wwAssB mr abs rep f = beforeBiR (whenJust (verifyAssB abs rep f) mr)
                                (\ () -> bidirectional wwBL wwBR)
  where
    assA :: BiRewriteH CoreExpr
    assA = wwAssA Nothing abs rep

    wwBL :: RewriteH CoreExpr
    wwBL = withPatFailMsg (wrongExprForm "abs (rep (f h x))") $
           do App _ (App _ (App (App f' _) _)) <- idR
              guardMsg (exprAlphaEq f f') "given body function does not match expression."
              forewardT assA

    wwBR :: RewriteH CoreExpr
    wwBR = withPatFailMsg (wrongExprForm "f h x") $
           do App (App f' _) _ <- idR
              guardMsg (exprAlphaEq f f') "given body function does not match expression."
              backwardT assA

-- | @abs (rep (f h x))@  \<==\>  @f h x@
wwB :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption B
    -> CoreString                -- ^ abs
    -> CoreString                -- ^ rep
    -> CoreString                -- ^ f
    -> BiRewriteH CoreExpr
wwB mr = parse3beforeBiR (wwAssB mr)

-- | @fix (X->A) (\ h x -> abs (rep (f h x)))@  \<==\>  @fix (X->A) f@
wwAssC :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption C
       -> CoreExpr                  -- ^ abs
       -> CoreExpr                  -- ^ rep
       -> CoreExpr                  -- ^ f
       -> BiRewriteH CoreExpr
wwAssC mr abs rep f = beforeBiR (do _ <- isFixExpr
                                    whenJust (verifyAssC abs rep f) mr
                                )
                                (\ () -> bidirectional wwCL wwCR)
  where
    assB :: BiRewriteH CoreExpr
    assB = wwAssB Nothing abs rep f

    wwCL :: RewriteH CoreExpr
    wwCL = wwAssAimpliesAssC (forewardT assB)

    wwCR :: RewriteH CoreExpr
    wwCR = appAllR idR (etaExpandR "h" >>> lamAllR idR (etaExpandR "x" >>> lamAllR idR (backwardT assB)))

-- | @fix (X->A) (\ h x -> abs (rep (f h x)))@  \<==\>  @fix (X->A) f@
wwC :: Maybe (RewriteH CoreExpr) -- ^ WW Assumption C
    -> CoreString                -- ^ abs
    -> CoreString                -- ^ rep
    -> CoreString                -- ^ f
    -> BiRewriteH CoreExpr
wwC mr = parse3beforeBiR (wwAssC mr)

--------------------------------------------------------------------------------------------------

verifyWWAss :: CoreExpr        -- ^ abs
            -> CoreExpr        -- ^ rep
            -> CoreExpr        -- ^ f
            -> WWAssumption
            -> TranslateH x ()
verifyWWAss abs rep f (WWAssumption tag ass) =
    case tag of
      A -> verifyAssA abs rep ass
      B -> verifyAssB abs rep f ass
      C -> verifyAssC abs rep f ass

verifyAssA :: CoreExpr          -- ^ abs
           -> CoreExpr          -- ^ rep
           -> RewriteH CoreExpr -- ^ WW Assumption A
           -> TranslateH x ()
verifyAssA abs rep assA =
  prefixFailMsg ("verification of worker/wrapper Assumption A failed: ") $
  do (tyA,_) <- absRepTypes abs rep
     a       <- constT (newIdH "a" tyA)
     let lhs = App abs (App rep (Var a))
         rhs = Var a
     verifyEqualityProofT lhs rhs assA

verifyAssB :: CoreExpr          -- ^ abs
           -> CoreExpr          -- ^ rep
           -> CoreExpr          -- ^ f
           -> RewriteH CoreExpr -- ^ WW Assumption B
           -> TranslateH x ()
verifyAssB abs rep f assB =
  prefixFailMsg ("verification of worker/wrapper assumption B failed: ") $
  do (tyA,_) <- absRepTypes abs rep
     tyXA     <- constT (endoFunType f)
     (tyX,tA) <- constT (splitFunTypeM tyXA)
     guardMsg (eqType tyA tA) "type of program body does not match types of abs/rep."
     h        <- constT (newIdH "h" tyXA)
     x        <- constT (newIdH "x" tyX)
     let lhs = App abs (App rep (App (App f (Var h)) (Var x)))
         rhs = App (App f (Var h)) (Var x)
     verifyEqualityProofT lhs rhs assB

verifyAssC :: CoreExpr          -- ^ abs
           -> CoreExpr          -- ^ rep
           -> CoreExpr          -- ^ f
           -> RewriteH CoreExpr -- ^ WW Assumption C
           -> TranslateH a ()
verifyAssC abs rep f assC =
  prefixFailMsg ("verification of worker/wrapper assumption C failed: ") $
  do (tyA,_)  <- absRepTypes abs rep
     tyXA     <- constT (endoFunType f)
     (tyX,tA) <- constT (splitFunTypeM tyXA)
     guardMsg (eqType tyA tA) "type of program body does not match types of abs/rep."
     h        <- constT (newIdH "h" tyXA)
     x        <- constT (newIdH "x" tyX)
     rhs      <- mkFix f
     lhs      <- mkFix (Lam h (Lam x (App abs (App rep (App (App f (Var h)) (Var x))))))
     verifyEqualityProofT lhs rhs assC

--------------------------------------------------------------------------------------------------

absRepTypes :: MonadCatch m => CoreExpr -> CoreExpr -> m (Type,Type)
absRepTypes abs rep = setFailMsg "given expressions have the wrong types to form a valid abs/rep pair." $
                      funsWithInverseTypes rep abs

--------------------------------------------------------------------------------------------------
