{-# LANGUAGE FlexibleContexts #-}
module HERMIT.Dictionary.New where

import Control.Arrow

import HERMIT.Context
import HERMIT.Core
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC
import HERMIT.ParserCore

import HERMIT.Dictionary.Local.Let hiding (externals)

externals ::  [External]
externals = map ((.+ Experiment) . (.+ TODO))
         [ external "var" (promoteExprT . isVar :: String -> TransformH LCore ())
                [ "var '<v> returns successfully for variable v, and fails otherwise."
                , "Useful in combination with \"when\", as in: when (var v) r"
                ] .+ Predicate
         , external "nonrec-intro" ((\ s str -> promoteCoreR (nonRecIntro s str)) :: String -> CoreString -> RewriteH LCore)
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
         ]

------------------------------------------------------------------------------------------------------

-- TODO:  We might not want to match on TyVars and CoVars here.
-- Probably better to have another predicate that operates on CoreTC, that way it can reach TyVars buried within types.
-- But given the current setup (using Core for most things), changing "var" to operate on CoreTC would make it incompatible with other combinators.
-- I'm not sure how to fix the current setup though.
-- isVar :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => String -> Transform c m CoreExpr ()
-- isVar nm = (varT matchName <+ typeT (tyVarT matchName) <+ coercionT (coVarCoT matchName))
--                  >>= guardM
--   where
--     matchName :: Monad m => Transform c m Var Bool
--     matchName = arr (cmpString2Var nm)

-- TODO: there might be a better module for this

-- | Test if the current expression is an identifier matching the given name.
isVar :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => String -> Transform c m CoreExpr ()
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
