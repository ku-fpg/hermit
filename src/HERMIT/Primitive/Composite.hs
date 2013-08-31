{-# LANGUAGE FlexibleContexts, ScopedTypeVariables #-}

module HERMIT.Primitive.Composite
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

import GhcPlugins as GHC hiding (varName)

import HERMIT.Context
import HERMIT.Core
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External

import HERMIT.Primitive.Debug hiding (externals)
import HERMIT.Primitive.GHC hiding (externals)
import HERMIT.Primitive.Inline hiding (externals)
import HERMIT.Primitive.Local hiding (externals)
import HERMIT.Primitive.Unfold hiding (externals)

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------------------------------

externals ::  [External]
externals =
    [ external "unfold-basic-combinator" (promoteExprR unfoldBasicCombinatorR :: RewriteH Core)
        [ "Unfold the current expression if it is one of the basic combinators: ($), (.), id, flip, const, fst or snd." ]
    , external "simplify" (simplifyR :: RewriteH Core)
        [ "innermost (unfold-basic-combinator <+ beta-reduce-plus <+ safe-let-subst <+ case-reduce <+ let-elim)" ]
    , external "bash" (bashR :: RewriteH Core)
        bashHelp .+ Eval .+ Deep .+ Loop
    , external "bash-extended-with" (bashExtendedWithR :: RewriteH Core -> RewriteH Core)
        [ "Run \"bash\" extended with an additional rewrite.",
          "Note: be sure that the new rewrite either fails or makes progress, else this may loop."
        ] .+ Eval .+ Deep .+ Loop
    , external "bash-debug" (bashDebugR :: RewriteH Core)
        [ "verbose bash - most useful with set-auto-corelint True" ] .+ Eval .+ Deep .+ Loop
    ]

------------------------------------------------------------------------------------------------------

-- | Unfold the current expression if it is one of the basic combinators: ('$'), ('.'), 'id', 'flip', 'const', 'fst' or 'snd'.
--   This is intended to be used as a component of simplification traversals such as 'simplifyR' or 'bashR'.
unfoldBasicCombinatorR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
unfoldBasicCombinatorR = setFailMsg "unfold-basic-combinator failed." $
     unfoldNameR (TH.mkName "$")
  <+ unfoldNameR (TH.mkName ".")
  <+ unfoldNameR (TH.mkName "id")
  <+ unfoldNameR (TH.mkName "flip")
  <+ unfoldNameR (TH.mkName "const")
  <+ unfoldNameR (TH.mkName "fst")
  <+ unfoldNameR (TH.mkName "snd")

simplifyR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM Core
simplifyR = setFailMsg "Simplify failed: nothing to simplify." $
    innermostR (   promoteBindR recToNonrecR
                <+ promoteExprR ( unfoldBasicCombinatorR
                               <+ betaReducePlusR
                               <+ safeLetSubstR
                               <+ caseReduceR
                               <+ letElimR )
               )

------------------------------------------------------------------------------------------------------

bashR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM Core
bashR = bashUsingR (map fst bashComponents)

bashExtendedWithR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM Core -> Rewrite c HermitM Core
bashExtendedWithR r = bashUsingR (r : map fst bashComponents)

bashDebugR :: RewriteH Core
bashDebugR = bashUsingR $ map (\ (r,nm) -> r >>> observeR nm) bashComponents

bashUsingR :: forall c m. (ExtendPath c Crumb, AddBindings c, MonadCatch m) => [Rewrite c m Core] -> Rewrite c m Core
bashUsingR rs =
    setFailMsg "bash failed: nothing to do." $
    readerT $ \ core1 -> occurAnalyseR >>> readerT (\ core2 -> if core1 `coreSyntaxEq` core2
                                                                 then bashCoreR      -- equal, no progress yet
                                                                 else tryR bashCoreR -- unequal, progress has already been made
                                                   )
  -- the changedByR combinator doesn't quite do what we need here
  where
    bashCoreR :: Rewrite c m Core
    bashCoreR = repeatR (innermostR (orR rs) >>> occurAnalyseR)

{-
Occurrence Analysis updates meta-data, as well as performing some basic simplifications.
occurAnalyseR always succeeds, whereas occurAnalyseChangedR fails is the result is alpha equivalent.
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

-- An alternative would be to use the type: Injection a Core => Rewrite c HermitM a
-- Then we wouldn't need the promote's everywhere, and could just apply promote in bashR.
-- I don't think it really matters much either way.

bashComponents :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => [(Rewrite c HermitM Core, String)]
bashComponents =
  [ (promoteExprR unfoldBasicCombinatorR, "unfold-basic-combinator")
  , (promoteExprR dezombifyR, "dezombify")
  , (promoteExprR inlineCaseAlternativeR, "inline-case-alternative")
  , (promoteExprR betaReducePlusR, "beta-reduce-plus")
  , (promoteExprR etaReduceR, "eta-reduce")
  , (promoteBindR recToNonrecR, "rec-to-nonrec")
  , (promoteExprR caseFloatAppR, "case-float-app")
  , (promoteExprR caseFloatCaseR, "case-float-case")
  , (promoteExprR caseFloatCastR, "case-float-cast")
  , (promoteExprR caseFloatLetR, "case-float-let")
  , (promoteExprR caseReduceR, "case-reduce")
  , (promoteExprR castElimReflR, "cast-elim-refl")
  , (promoteExprR castElimSymR, "cast-elim-sym")
  , (promoteExprR safeLetSubstR, "safe-let-subst")
--  , (promoteExprR letElimR, "let-elim")  -- This may not need to be in bash, as it's subsumed by occurrence analysis.
  , (promoteExprR letFloatAppR, "let-float-app")     -- O(n)
  , (promoteExprR letFloatArgR, "let-float-arg")     -- O(n)
  , (promoteExprR letFloatLamR, "let-float-lam")     -- O(n)
  , (promoteExprR letFloatLetR, "let-float-let")     -- O(n)
  , (promoteExprR letFloatCaseR, "let-float-case")   -- O(n)
  , (promoteExprR letFloatCastR, "let-float-cast")   -- O(1)
  , (promoteProgR letFloatTopR, "let-float-top")
  ]

------------------------------------------------------------------------------------------------------

