{-# LANGUAGE FlexibleContexts, MultiWayIf #-}
module HERMIT.Primitive.New where

import Control.Arrow

import HERMIT.Context
import HERMIT.Core
import HERMIT.Monad
import HERMIT.Kure
import HERMIT.External
import HERMIT.GHC
import HERMIT.ParserCore

import qualified Language.Haskell.TH as TH

externals ::  [External]
externals = map ((.+ Experiment) . (.+ TODO))
         [ external "var" (promoteExprT . isVar :: TH.Name -> TranslateH Core ())
                [ "var '<v> returns successfully for variable v, and fails otherwise.",
                  "Useful in combination with \"when\", as in: when (var v) r" ] .+ Predicate
         , external "prog-nonrec-intro" ((\ nm core -> promoteProgR $ progNonRecIntroR (show nm) core) :: TH.Name -> CoreString -> RewriteH Core)
                [ "Introduce a new top-level definition."
                , "prog-nonrec-into 'v [| e |]"
                , "prog ==> ProgCons (v = e) prog" ] .+ Introduce .+ Shallow
         , external "let-nonrec-intro" ((\ nm core -> promoteExprR $ letNonRecIntroR (show nm) core) :: TH.Name -> CoreString -> RewriteH Core)
                [ "Introduce a new definition as a non-recursive let binding."
                , "let-nonrec-intro 'v [| e |]"
                , "body ==> let v = e in body" ] .+ Introduce .+ Shallow
         ]

------------------------------------------------------------------------------------------------------

-- TODO:  We might not want to match on TyVars and CoVars here.
-- Probably better to have another predicate that operates on CoreTC, that way it can reach TyVars buried within types.
-- But given the current setup (using Core for most things), changing "var" to operate on CoreTC would make it incompatible with other combinators.
-- I'm not sure how to fix the current setup though.
-- isVar :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => TH.Name -> Translate c m CoreExpr ()
-- isVar nm = (varT matchName <+ typeT (tyVarT matchName) <+ coercionT (coVarCoT matchName))
--                  >>= guardM
--   where
--     matchName :: Monad m => Translate c m Var Bool
--     matchName = arr (cmpTHName2Var nm)

-- TODO: there might be a better module for this

-- | Test if the current expression is an identifier matching the given name.
isVar :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => TH.Name -> Translate c m CoreExpr ()
isVar nm = varT (arr $ cmpTHName2Var nm) >>= guardM

------------------------------------------------------------------------------------------------------

-- The types of these can probably be generalised after the Core Parser is generalised.

-- | @prog@ ==> @'ProgCons' (v = e) prog@
progNonRecIntroR :: String -> CoreString -> RewriteH CoreProg
progNonRecIntroR nm expr =
  do e <- parseCoreExprT expr
     guardMsg (not $ isTyCoArg e) "Top-level type or coercion definitions are prohibited."
     -- TODO: if e is not type-correct, then exprType will crash.
     --       Proposal: parseCore should check that its result is (locally) well-typed
     contextfreeT $ \ prog -> do i <- newIdH nm (exprType e)
                                 return $ ProgCons (NonRec i e) prog

-- | @body@ ==> @let v = e in body@
letNonRecIntroR :: String -> CoreString -> RewriteH CoreExpr
letNonRecIntroR nm expr =
  do e <- parseCoreExprT expr
     -- TODO: if e is not type-correct, then exprTypeOrKind will crash.
     --       Proposal: parseCore should check that its result is (locally) well-typed
     contextfreeT $ \ body -> do let tyk = exprKindOrType e
                                 v <- if | isTypeArg e  -> newTyVarH nm tyk
                                         | isCoArg e    -> newCoVarH nm tyk
                                         | otherwise    -> newIdH nm tyk
                                 return $ Let (NonRec v e) body

------------------------------------------------------------------------------------------------------
