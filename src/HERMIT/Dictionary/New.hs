{-# LANGUAGE CPP, FlexibleContexts #-}
module HERMIT.Dictionary.New where

import Control.Arrow

import HERMIT.Context
import HERMIT.Core
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC
#if __GLASGOW_HASKELL__ > 706
import HERMIT.Monad
#endif
import HERMIT.ParserCore

#if __GLASGOW_HASKELL__ > 706
import HERMIT.Dictionary.Composite hiding (externals)
import HERMIT.Dictionary.Debug hiding (externals)
#endif
import HERMIT.Dictionary.Local.Let hiding (externals)

externals ::  [External]
externals = map ((.+ Experiment) . (.+ TODO))
         [ external "var" (promoteExprT . isVar :: String -> TranslateH Core ())
                [ "var '<v> returns successfully for variable v, and fails otherwise."
                , "Useful in combination with \"when\", as in: when (var v) r"
                ] .+ Predicate
         , external "nonrec-intro" (nonRecIntro :: String -> CoreString -> RewriteH Core)
                [ "Introduce a new non-recursive binding.  Only works at Expression or Program nodes."
                , "nonrec-into 'v [| e |]"
                , "body ==> let v = e in body"
                ] .+ Introduce .+ Shallow
         -- , external "prog-nonrec-intro" ((\ nm core -> promoteProgR $ progNonRecIntro nm core) :: String -> CoreString -> RewriteH Core)
         --        [ "Introduce a new top-level definition."
         --        , "prog-nonrec-into 'v [| e |]"
         --        , "prog ==> ProgCons (v = e) prog" ] .+ Introduce .+ Shallow
         -- , external "let-nonrec-intro" ((\ nm core -> promoteExprR $ letNonRecIntro nm core) :: String -> CoreString -> RewriteH Core)
         --        [ "Introduce a new definition as a non-recursive let binding."
         --        , "let-nonrec-intro 'v [| e |]"
         --        , "body ==> let v = e in body" ] .+ Introduce .+ Shallow
#if __GLASGOW_HASKELL__ > 706
         , external "replace-typeable-int-list" (promoteExprR (return (mkListTy intTy) >>> buildTypeableT) :: RewriteH Core)
                [ "test building a dictionary" ]
#endif
         ]

------------------------------------------------------------------------------------------------------

-- TODO:  We might not want to match on TyVars and CoVars here.
-- Probably better to have another predicate that operates on CoreTC, that way it can reach TyVars buried within types.
-- But given the current setup (using Core for most things), changing "var" to operate on CoreTC would make it incompatible with other combinators.
-- I'm not sure how to fix the current setup though.
-- isVar :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => String -> Translate c m CoreExpr ()
-- isVar nm = (varT matchName <+ typeT (tyVarT matchName) <+ coercionT (coVarCoT matchName))
--                  >>= guardM
--   where
--     matchName :: Monad m => Translate c m Var Bool
--     matchName = arr (cmpString2Var nm)

-- TODO: there might be a better module for this

-- | Test if the current expression is an identifier matching the given name.
isVar :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => String -> Translate c m CoreExpr ()
isVar nm = varT (arr $ cmpString2Var nm) >>= guardM

------------------------------------------------------------------------------------------------------

-- The types of these can probably be generalised after the Core Parser is generalised.

-- | @prog@ ==> @'ProgCons' (v = e) prog@
nonRecIntro :: String -> CoreString -> RewriteH Core
nonRecIntro nm expr = parseCoreExprT expr >>= nonRecIntroR nm
     -- TODO: if e is not type-correct, then exprType will crash.
     --       Proposal: parseCore should check that its result is (locally) well-typed


-- -- | @prog@ ==> @'ProgCons' (v = e) prog@
-- progNonRecIntro :: String -> CoreString -> RewriteH CoreProg
-- progNonRecIntro nm expr = parseCoreExprT expr >>= progNonRecIntroR nm
--      -- TODO: if e is not type-correct, then exprType will crash.
--      --       Proposal: parseCore should check that its result is (locally) well-typed

-- -- | @body@ ==> @let v = e in body@
-- letNonRecIntro :: String -> CoreString -> RewriteH CoreExpr
-- letNonRecIntro nm expr = parseCoreExprT expr >>= letNonRecIntroR nm
--      -- TODO: if e is not type-correct, then exprTypeOrKind will crash.
--      --       Proposal: parseCore should check that its result is (locally) well-typed


------------------------------------------------------------------------------------------------------

#if __GLASGOW_HASKELL__ > 706
buildTypeableT :: TranslateH Type CoreExpr
buildTypeableT = do
    (i, bnds) <- contextfreeT $ \ t -> getModGuts >>= liftCoreM . flip buildTypeable t
    return (mkCoreLets bnds (varToCoreExpr i)) >>> tryR (extractR simplifyR) >>> observeR "buildTypeableT result"
#endif

