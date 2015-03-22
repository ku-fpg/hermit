{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Dictionary.Composite
    ( externals
    , unfoldBasicCombinatorR
    , simplifyR
    , bashUsingR
    , bashR
    , bashExtendedWithR
    , bashDebugR
    , smashR
    , smashUsingR
    , smashExtendedWithR
    ) where

import Control.Arrow
import Control.Monad

import Data.String (fromString)

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.Debug hiding (externals)
import HERMIT.Dictionary.GHC hiding (externals)
import HERMIT.Dictionary.Inline hiding (externals)
import HERMIT.Dictionary.Local hiding (externals)
import HERMIT.Dictionary.Unfold hiding (externals)

------------------------------------------------------------------------------------------------------

externals ::  [External]
externals =
    [ external "unfold-basic-combinator" (promoteExprR unfoldBasicCombinatorR :: RewriteH LCore)
        [ "Unfold the current expression if it is one of the basic combinators:"
        , "($), (.), id, flip, const, fst, snd, curry, and uncurry." ]
    , external "simplify" (simplifyR :: RewriteH LCore)
        [ "innermost (unfold-basic-combinator <+ beta-reduce-plus <+ safe-let-subst <+ case-reduce <+ let-elim)" ]
    , external "bash" (bashR :: RewriteH LCore)
        bashHelp .+ Eval .+ Deep .+ Loop
    , external "smash" (smashR :: RewriteH LCore)
        smashHelp .+ Eval .+ Deep .+ Loop .+ Experiment
    , external "bash-extended-with" (bashExtendedWithR :: [RewriteH LCore] -> RewriteH LCore)
        [ "Run \"bash\" extended with additional rewrites.",
          "Note: be sure that the new rewrite either fails or makes progress, else this may loop."
        ] .+ Eval .+ Deep .+ Loop
    , external "smash-extended-with" (smashExtendedWithR :: [RewriteH LCore] -> RewriteH LCore)
        [ "Run \"smash\" extended with additional rewrites.",
          "Note: be sure that the new rewrite either fails or makes progress, else this may loop."
        ] .+ Eval .+ Deep .+ Loop
    , external "bash-debug" (bashDebugR :: RewriteH LCore)
        [ "verbose bash - most useful with set-auto-corelint True" ] .+ Eval .+ Deep .+ Loop
    ]

------------------------------------------------------------------------------------------------------

basicCombinators :: [HermitName]
basicCombinators = map fromString ["$",".","id","flip","const","fst","snd","curry","uncurry"]

-- | Unfold the current expression if it is one of the basic combinators:
-- ('$'), ('.'), 'id', 'flip', 'const', 'fst', 'snd', 'curry', and 'uncurry'.
--   This is intended to be used as a component of simplification traversals such as 'simplifyR' or 'bashR'.
unfoldBasicCombinatorR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
                          , MonadCatch m )
                       => Rewrite c m CoreExpr
unfoldBasicCombinatorR = setFailMsg "unfold-basic-combinator failed." $ orR (map f basicCombinators)
    where f nm = voidM (callNameT nm) >> voidM callSaturatedT >> unfoldR
          voidM = liftM (const ()) -- can't wait for AMP

simplifyR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadBindings c, ReadPath c Crumb
             , MonadCatch m, MonadUnique m )
          => Rewrite c m LCore
simplifyR = setFailMsg "Simplify failed: nothing to simplify." $
    innermostR (   promoteBindR recToNonrecR
                <+ promoteExprR ( unfoldBasicCombinatorR
                               <+ betaReducePlusR
                               <+ letNonRecSubstSafeR
                               <+ caseReduceR False
                               <+ letElimR )
               )

------------------------------------------------------------------------------------------------------

-- | Bash is intended as a general-purpose cleanup/simplification command.
-- It performs rewrites such as let floating, case floating, and case elimination, when safe.
-- It also performs dead binding elimination and case reduction, and unfolds a number of
-- basic combinators. See 'bashComponents' for a list of rewrites performed.
-- Bash also performs occurrence analysis and de-zombification on the result, to update
-- IdInfo attributes relied-upon by GHC.
bashR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadBindings c, ReadPath c Crumb
         , MonadCatch m, MonadUnique m )
      => Rewrite c m LCore
bashR = bashExtendedWithR []

-- | An extensible bash. Given rewrites are performed before normal bash rewrites.
bashExtendedWithR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadBindings c, ReadPath c Crumb
                     , MonadCatch m, MonadUnique m )
                  => [Rewrite c m LCore] -> Rewrite c m LCore
bashExtendedWithR rs = bashUsingR (rs ++ map fst bashComponents)

-- | Like 'bashR', but outputs name of each successful sub-rewrite, providing a log.
-- Also performs core lint on the result of a successful sub-rewrite.
-- If core lint fails, shows core fragment before and after the sub-rewrite which introduced the problem.
-- Note: core fragment which fails linting is still returned! Otherwise would behave differently than bashR.
-- Useful for debugging the bash command itself.
bashDebugR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadBindings c, ReadPath c Crumb
              , HasDebugChan m, HasDynFlags m, MonadCatch m, MonadUnique m )
           => Rewrite c m LCore
bashDebugR = bashUsingR [ bracketR nm r >>> catchM (promoteT lintExprT >> idR) traceR
                        | (r,nm) <- bashComponents ]

-- | Perform the 'bash' algorithm with a given list of rewrites.
bashUsingR :: (AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadPath c Crumb, MonadCatch m)
           => [Rewrite c m LCore] -> Rewrite c m LCore
bashUsingR rs = setFailMsg "bash failed: nothing to do." $
    repeatR (occurAnalyseR >>> onetdR (catchesT rs)) >+> anytdR (promoteExprR dezombifyR) >+> occurAnalyseChangedR

{-
Occurrence Analysis updates meta-data, as well as performing some basic simplifications.
occurAnalyseR always succeeds, whereas occurAnalyseChangedR fails is the result is syntactically equivalent.
The awkwardness is because:
  - we want bash to fail if nothing changes
  - we want bash to succeed if the result is not syntactically-equivalent
    (ideally, if any changes are made at all, but that's not the case yet)
  - we want bash to update the meta-data
  - after running bash there should be nothing left to do (i.e. an immediately subsequent bash should always fail)

Also, it's still possible for some meta-data to be out-of-date after bash, despite the case analysis.
For example, if the focal point is a case-alt rhs, this won't update the identifer info of variables
bound in the alternative.
-}

bashHelp :: [String]
bashHelp = "Iteratively apply the following rewrites until nothing changes:"
         : map snd (bashComponents :: [(RewriteH LCore,String)] -- to resolve ambiguity
                                                                                       )
-- TODO: Think about a good order for bash.
bashComponents :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
                  , MonadCatch m, MonadUnique m )
               => [(Rewrite c m LCore, String)]
bashComponents =
  [ -- (promoteExprR occurAnalyseExprChangedR, "occur-analyse-expr")    -- ??
    (promoteExprR betaReduceR, "beta-reduce")                        -- O(1)
  , (promoteExprR (caseReduceR True), "case-reduce")                 -- O(n)
  , (promoteExprR (caseReduceUnfoldR True), "case-reduce-unfold")    -- O(n)
  , (promoteExprR caseElimSeqR, "case-elim-seq")
  , (promoteExprR unfoldBasicCombinatorR, "unfold-basic-combinator") -- O(n)
  , (promoteExprR inlineCaseAlternativeR, "inline-case-alternative") -- O(n)
  , (promoteExprR etaReduceR, "eta-reduce")                          -- O(n)
--  , (promoteBindR recToNonrecR, "rec-to-nonrec")                     -- O(n) -- subsumed by occurrence analysis
  , (promoteExprR letNonRecSubstSafeR, "let-nonrec-subst-safe")      -- O(n)
  , (promoteExprR caseFloatAppR, "case-float-app")                   -- O(n)
  , (promoteExprR caseFloatCaseR, "case-float-case")                 -- O(n)
  , (promoteExprR caseFloatLetR, "case-float-let")                   -- O(n) but usually O(1)
  , (promoteExprR caseFloatCastR, "case-float-cast")                 -- O(1)
--  , (promoteExprR letElimR, "let-elim")  -- O(n^2) -- Subsumed by occurrence analysis.
  , (promoteExprR letFloatAppR, "let-float-app")                     -- O(n)
  , (promoteExprR letFloatArgR, "let-float-arg")                     -- O(n)
  , (promoteExprR letFloatLamR, "let-float-lam")                     -- O(n)
  , (promoteExprR letFloatLetR, "let-float-let")                     -- O(n)
  , (promoteExprR letFloatCaseR, "let-float-case")                   -- O(n)
  , (promoteExprR letFloatCastR, "let-float-cast")                   -- O(1)
  , (promoteProgR letFloatTopR, "let-float-top")                     -- O(n)
  , (promoteExprR castElimReflR, "cast-elim-refl")                   -- O(1)
  , (promoteExprR castElimSymR, "cast-elim-sym")                     -- O(1)
--  , (promoteExprR dezombifyR, "dezombify")                           -- O(1) -- performed at the end
  ]


------------------------------------------------------------------------------------------------------

-- | Smash is a more powerful but less efficient version of bash.
-- Unlike bash, smash is not concerned with whether it duplicates work,
-- and is intended for use during proving tasks.
smashR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadBindings c, ReadPath c Crumb
          , MonadCatch m, MonadUnique m )
       => Rewrite c m LCore
smashR = smashExtendedWithR []

smashExtendedWithR :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, LemmaContext c, ReadBindings c, ReadPath c Crumb
                      , MonadCatch m, MonadUnique m )
                   => [Rewrite c m LCore] -> Rewrite c m LCore
smashExtendedWithR rs = smashUsingR (rs ++ map fst smashComponents1) (map fst smashComponents2)


smashUsingR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, LemmaContext c, MonadCatch m) => [Rewrite c m LCore] -> [Rewrite c m LCore] -> Rewrite c m LCore
smashUsingR rs1 rs2 =
    setFailMsg "smash failed: nothing to do." $
    repeatR (occurAnalyseR >>> (onetdR (catchesT rs1) <+ onetdR (catchesT rs2))) >+> anytdR (promoteExprR dezombifyR) >+> occurAnalyseChangedR


smashHelp :: [String]
smashHelp = "A more powerful but less efficient version of \"bash\", intended for use while proving lemmas.  Iteratively apply the following rewrites until nothing changes:" : map snd (smashComponents1 ++ smashComponents2
                                                                                           :: [(RewriteH LCore,String)] -- to resolve ambiguity
                                                                                        )


-- | As bash, but with "let-nonrec-subst" instead of "let-nonrec-subst-safe".
smashComponents1 :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
                    , MonadCatch m, MonadUnique m )
                 => [(Rewrite c m LCore, String)]
smashComponents1 =
  [ -- (promoteExprR occurAnalyseExprChangedR, "occur-analyse-expr")    -- ??
    (promoteExprR betaReduceR, "beta-reduce")                        -- O(1)
  , (promoteExprR (caseReduceR True), "case-reduce")                 -- O(n)
  , (promoteExprR (caseReduceUnfoldR True), "case-reduce-unfold")    -- O(n)
  , (promoteExprR caseElimSeqR, "case-elim-seq")
  , (promoteExprR unfoldBasicCombinatorR, "unfold-basic-combinator") -- O(n)
  , (promoteExprR inlineCaseAlternativeR, "inline-case-alternative") -- O(n)
  , (promoteExprR etaReduceR, "eta-reduce")                          -- O(n)
--  , (promoteBindR recToNonrecR, "rec-to-nonrec")                     -- O(n) -- subsumed by occurrence analysis
  , (promoteExprR letNonRecSubstR, "let-nonrec-subst")               -- O(n)
  , (promoteExprR caseFloatAppR, "case-float-app")                   -- O(n)
  , (promoteExprR caseFloatCaseR, "case-float-case")                 -- O(n)
  , (promoteExprR caseFloatLetR, "case-float-let")                   -- O(n) but usually O(1)
  , (promoteExprR caseFloatCastR, "case-float-cast")                 -- O(1)
--  , (promoteExprR letElimR, "let-elim")  -- O(n^2) -- Subsumed by occurrence analysis.
  , (promoteExprR letFloatAppR, "let-float-app")                     -- O(n)
  , (promoteExprR letFloatArgR, "let-float-arg")                     -- O(n)
  , (promoteExprR letFloatLamR, "let-float-lam")                     -- O(n)
  , (promoteExprR letFloatLetR, "let-float-let")                     -- O(n)
  , (promoteExprR letFloatCaseR, "let-float-case")                   -- O(n)
  , (promoteExprR letFloatCastR, "let-float-cast")                   -- O(1)
  , (promoteProgR letFloatTopR, "let-float-top")                     -- O(n)
  , (promoteExprR castElimReflR, "cast-elim-refl")                   -- O(1)
  , (promoteExprR castElimSymR, "cast-elim-sym")                     -- O(1)
  , (promoteExprR castFloatAppR, "cast-float-app")                   -- O(1)
  , (promoteExprR castFloatLamR, "cast-float-lam")                   -- O(1)
--  , (promoteExprR dezombifyR, "dezombify")                           -- O(1) -- performed at the end
  ]

smashComponents2 :: ( ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c
                    , MonadCatch m, MonadUnique m )
                 => [(Rewrite c m LCore, String)]
smashComponents2 =
    [ (promoteExprR caseElimMergeAltsR, "case-elim-merge-alts") -- do this last, lest it prevent other simplifications
    ]
