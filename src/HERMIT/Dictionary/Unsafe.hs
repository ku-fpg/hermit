module HERMIT.Dictionary.Unsafe
    ( externals
    , unsafeReplaceR
    ) where

import Control.Monad

import HERMIT.Core
import HERMIT.Kure
import HERMIT.GHC
import HERMIT.External
import HERMIT.ParserCore

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: [External]
externals = map (.+ Unsafe)
    [ external "unsafe-replace" (promoteExprR . unsafeReplaceR :: CoreString -> RewriteH LCore)
        [ "replace the currently focused expression with a new expression"
        , "DOES NOT ensure that free variables in the replacement expression are in scope" ]
    ]

------------------------------------------------------------------------

unsafeReplaceR :: CoreString -> RewriteH CoreExpr
unsafeReplaceR core =
    transform $ \ c e -> do
        e' <- parseCore core c
        guardMsg (eqType (exprKindOrType e) (exprKindOrType e')) "expression types differ."
        return e'

------------------------------------------------------------------------
