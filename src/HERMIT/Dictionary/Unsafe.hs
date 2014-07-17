module HERMIT.Dictionary.Unsafe
    ( externals
    , unsafeReplaceR
    , unsafeReplaceStashR
    ) where

import Control.Monad

import HERMIT.Core
import HERMIT.Kure
import HERMIT.GHC
import HERMIT.Monad
import HERMIT.External
import HERMIT.ParserCore

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: [External]
externals = map (.+ Unsafe)
    [ external "unsafe-replace" (promoteExprR . unsafeReplaceR :: CoreString -> RewriteH Core)
        [ "replace the currently focused expression with a new expression"
        , "DOES NOT ensure that free variables in the replacement expression are in scope" ]
    , external "unsafe-replace" (promoteExprR . unsafeReplaceStashR :: RememberedName -> RewriteH Core)
        [ "replace the currently focused expression with a remembered expression"
        , "DOES NOT ensure that free variables in the replacement expression are in scope" ]
    ]

------------------------------------------------------------------------

unsafeReplaceR :: CoreString -> RewriteH CoreExpr
unsafeReplaceR core =
    transform $ \ c e -> do
        e' <- parseCore core c
        guardMsg (eqType (exprKindOrType e) (exprKindOrType e')) "expression types differ."
        return e'

unsafeReplaceStashR :: RememberedName -> RewriteH CoreExpr
unsafeReplaceStashR label = prefixFailMsg "unsafe-replace failed: " $
    contextfreeT $ \ e -> do
        Def _ rhs <- lookupDef label
        guardMsg (eqType (exprKindOrType e) (exprKindOrType rhs)) "expression types differ."
        return rhs

------------------------------------------------------------------------
