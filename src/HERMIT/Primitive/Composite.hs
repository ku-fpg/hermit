{-# LANGUAGE FlexibleContexts #-}
module HERMIT.Primitive.Composite
    ( externals
    , simplifyR
    , unfoldBasicCombinatorR
    ) where

import GhcPlugins as GHC hiding (varName)

import HERMIT.Context
import HERMIT.Core
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External

import HERMIT.Primitive.Local hiding (externals)
import HERMIT.Primitive.Unfold hiding (externals)

import qualified Language.Haskell.TH as TH

externals ::  [External]
externals = map ((.+ Experiment) . (.+ TODO))
    [ external "unfold-basic-combinator" (promoteExprR unfoldBasicCombinatorR :: RewriteH Core)
        [ "Unfold the current expression if it is one of the basic combinators: ($), (.) or id." ] .+ Bash
    , external "simplify" (simplifyR :: RewriteH Core)
        [ "innermost (unfold-basic-combinator <+ beta-reduce-plus <+ safe-let-subst <+ case-reduce <+ let-elim)" ]
    ]

------------------------------------------------------------------------------------------------------

-- | Unfold the current expression if it is one of the basic combinators: ('$'), ('.'), 'id', 'flip', 'const', 'fst' or 'snd'.
--   This is intended to be used as a component of simplification traversals such as 'simplifyR' or 'HERMIT.Dictionary.bashR'.
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

