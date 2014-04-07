{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Dictionary.Composite
    ( externals
    , unfoldBasicCombinatorR
    , simplifyR
    , bashUsingR
    , bashR
    , bashExtendedWithR
    , bashDebugR
    )
where

import Control.Arrow

import HERMIT.Context
import HERMIT.Core
import HERMIT.GHC
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External

import HERMIT.Dictionary.Debug hiding (externals)
import HERMIT.Dictionary.GHC hiding (externals)
import HERMIT.Dictionary.Inline hiding (externals)
import HERMIT.Dictionary.Local hiding (externals)
import HERMIT.Dictionary.Unfold hiding (externals)

------------------------------------------------------------------------------------------------------

externals ::  [External]
externals =
    [ external "unfold-basic-combinator" (promoteExprR unfoldBasicCombinatorR :: RewriteH Core)
        [ "Unfold the current expression if it is one of the basic combinators: ($), (.), id, flip, const, fst or snd." ]
    , external "simplify" (simplifyR :: RewriteH Core)
        [ "innermost (unfold-basic-combinator <+ beta-reduce-plus <+ safe-let-subst <+ case-reduce <+ let-elim)" ]
    , external "bash" (bashR :: RewriteH Core)
        bashHelp .+ Eval .+ Deep .+ Loop
    , external "smash" (smashR :: RewriteH Core)
        smashHelp .+ Eval .+ Deep .+ Loop .+ Experiment
    , external "bash-extended-with" (bashExtendedWithR :: [RewriteH Core] -> RewriteH Core)
        [ "Run \"bash\" extended with additional rewrites.",
          "Note: be sure that the new rewrite either fails or makes progress, else this may loop."
        ] .+ Eval .+ Deep .+ Loop
    , external "smash-extended-with" (smashExtendedWithR :: [RewriteH Core] -> RewriteH Core)
        [ "Run \"smash\" extended with additional rewrites.",
          "Note: be sure that the new rewrite either fails or makes progress, else this may loop."
        ] .+ Eval .+ Deep .+ Loop
    , external "bash-debug" (bashDebugR :: RewriteH Core)
        [ "verbose bash - most useful with set-auto-corelint True" ] .+ Eval .+ Deep .+ Loop
    ]

------------------------------------------------------------------------------------------------------

basicCombinators :: [String]
basicCombinators = ["$",".","id","flip","const","fst","snd","curry","uncurry"]

-- | Unfold the current expression if it is one of the basic combinators: ('$'), ('.'), 'id', 'flip', 'const', 'fst' or 'snd'.
--   This is intended to be used as a component of simplification traversals such as 'simplifyR' or 'bashR'.
unfoldBasicCombinatorR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => Rewrite c HermitM CoreExpr
unfoldBasicCombinatorR = setFailMsg "unfold-basic-combinator failed." $
     unfoldNamesR basicCombinators

simplifyR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => Rewrite c HermitM Core
simplifyR = setFailMsg "Simplify failed: nothing to simplify." $
    innermostR (   promoteBindR recToNonrecR
                <+ promoteExprR ( unfoldBasicCombinatorR
                               <+ betaReducePlusR
                               <+ letNonRecSubstSafeR
                               <+ caseReduceR False
                               <+ letElimR )
               )

------------------------------------------------------------------------------------------------------

bashR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => Rewrite c HermitM Core
bashR = bashExtendedWithR []

bashExtendedWithR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => [Rewrite c HermitM Core] -> Rewrite c HermitM Core
bashExtendedWithR rs = bashUsingR (rs ++ map fst bashComponents)


smashR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => Rewrite c HermitM Core
smashR = smashExtendedWithR []

smashExtendedWithR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => [Rewrite c HermitM Core] -> Rewrite c HermitM Core
smashExtendedWithR rs = smashUsingR (rs ++ map fst smashComponents1) (map fst smashComponents2)


-- | Like bashR, but outputs name of each successful sub-rewrite, providing a log.
-- Also performs core lint on the result of a successful sub-rewrite.
-- If core lint fails, shows core fragment before and after the sub-rewrite which introduced the problem.
-- Note: core fragment which fails linting is still returned! Otherwise would behave differently than bashR.
-- Useful for debugging the bash command itself.
bashDebugR :: RewriteH Core
bashDebugR = bashUsingR [ idR >>= \e -> r >>> traceR nm >>> (catchM (promoteT lintExprT >> idR)
                                                                    (\s -> do _ <- return e >>> observeR "[before]"
                                                                              observeR ("[" ++ nm ++ "]\n" ++ s)))
                        | (r,nm) <- bashComponents ]

-- bashUsingR :: forall c m. (ExtendPath c Crumb, AddBindings c, MonadCatch m) => [Rewrite c m Core] -> Rewrite c m Core
-- bashUsingR rs =
--     setFailMsg "bash failed: nothing to do." $
--     readerT $ \ core1 -> occurAnalyseR >>> readerT (\ core2 -> if core1 `coreSyntaxEq` core2
--                                                                  then bashCoreR      -- equal, no progress yet
--                                                                  else tryR bashCoreR -- unequal, progress has already been made
--                                                    )
--   -- the changedByR combinator doesn't quite do what we need here
--   where
--     bashCoreR :: Rewrite c m Core
--     bashCoreR = repeatR (innermostR (catchesT rs) >>> occurAnalyseR)

bashUsingR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m) => [Rewrite c m Core] -> Rewrite c m Core
bashUsingR rs =
    setFailMsg "bash failed: nothing to do." $
    repeatR (occurAnalyseR >>> onetdR (catchesT rs)) >+> anytdR (promoteExprR dezombifyR) >+> occurAnalyseChangedR

smashUsingR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m) => [Rewrite c m Core] -> [Rewrite c m Core] -> Rewrite c m Core
smashUsingR rs1 rs2 =
    setFailMsg "smash failed: nothing to do." $
    repeatR (occurAnalyseR >>> (onetdR (catchesT rs1) <+ onetdR (catchesT rs2))) >+> anytdR (promoteExprR dezombifyR) >+> occurAnalyseChangedR


 --   occurAnalyseChangedR >+> (innermostR (catchesT rs) >>> occurAnalyseR)

{-
Occurrence Analysis updates meta-data, as well as performing some basic simplifications.
occurAnalyseR always succeeds, whereas occurAnalyseChangedR fails is the result is syntactically equivalent.
The awkwardness is because:
  - we want bash to fail if nothing changes
  - we want bash to succeed if the result is not syntactically-equivalent (ideally, if any changes are made at all, but that's not the case yet)
  - we want bash to update the meta-data
  - after running bash there should be nothing left to do (i.e. an immediately subsequent bash should always fail)

Also, it's still possible for some meta-data to be out-of-date after bash, despite the case analysis.  For example, if the focal point is a case-alt rhs, this won't update the identifer info of variables bound in the alternative.
-}

bashHelp :: [String]
bashHelp = "Iteratively apply the following rewrites until nothing changes:" : map snd (bashComponents
                                                                                         :: [(RewriteH Core,String)] -- to resolve ambiguity
                                                                                       )

-- TODO: Think about a good order for bash.
bashComponents :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => [(Rewrite c HermitM Core, String)]
bashComponents =
  [ -- (promoteExprR occurAnalyseExprChangedR, "occur-analyse-expr")    -- ??
    (promoteExprR betaReduceR, "beta-reduce")                        -- O(1)
  , (promoteExprR (caseReduceR True), "case-reduce")                 -- O(n)
  , (promoteExprR (caseReduceIdR True), "case-reduce-id")            -- O(n)
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


smashHelp :: [String]
smashHelp = "A more powerful but less efficient version of \"bash\", intended for use while proving lemmas.  Iteratively apply the following rewrites until nothing changes:" : map snd (smashComponents1 ++ smashComponents2
                                                                                           :: [(RewriteH Core,String)] -- to resolve ambiguity
                                                                                        )


-- | As bash, but with "let-nonrec-subst" instead of "let-nonrec-subst-safe".
smashComponents1 :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => [(Rewrite c HermitM Core, String)]
smashComponents1 =
  [ -- (promoteExprR occurAnalyseExprChangedR, "occur-analyse-expr")    -- ??
    (promoteExprR betaReduceR, "beta-reduce")                        -- O(1)
  , (promoteExprR (caseReduceR True), "case-reduce")                 -- O(n)
  , (promoteExprR (caseReduceIdR True), "case-reduce-id")            -- O(n)
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
--  , (promoteExprR dezombifyR, "dezombify")                           -- O(1) -- performed at the end
  ]

smashComponents2 :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, ReadBindings c, HasEmptyContext c) => [(Rewrite c HermitM Core, String)]
smashComponents2 =
  [
    (promoteExprR caseElimMergeAltsR, "case-elim-merge-alts") -- do this last, lest it prevent other simplifications
  ]


-- (beta-reduce <+ case-reduce <+ case-reduce-id <+ case-elim-seq <+ unfold-basic-combinator <+ inline-case-alternative <+ eta-reduce <+ let-subst <+ case-float-app <+ case-float-case <+ case-float-let <+ case-float-cast <+ let-float-app <+ let-float-arg <+ let-float-lam <+ let-float-let <+ let-float-case <+ let-float-cast <+ let-float-top <+ cast-elim-refl <+ cast-elim-sym

------------------------------------------------------------------------------------------------------

