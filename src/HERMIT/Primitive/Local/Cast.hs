{-# LANGUAGE FlexibleContexts #-}

module HERMIT.Primitive.Local.Cast
    ( -- * Rewrites on Case Expressions
      externals
    , castElimRefl
    , castElimSym
    , castFloatApp
    , castElimSymPlus -- TODO: revisit
    ) where

import GhcPlugins
import qualified Coercion (substCo, extendTvSubst)
import Pair

import Control.Arrow
import Control.Monad

import HERMIT.Core
import HERMIT.Context
import HERMIT.Kure
import HERMIT.External

import HERMIT.Primitive.Common

------------------------------------------------------------------------------

-- | Externals relating to Case expressions.
externals :: [External]
externals =
    [ external "cast-elim" (promoteExprR castElim :: RewriteH Core)
        [ "cast-elim-refl <+ cast-elim-sym" ] .+ Shallow -- don't include in "Bash", as sub-rewrites are tagged "Bash" already.
    , external "cast-elim-refl" (promoteExprR castElimRefl :: RewriteH Core)
        [ "cast e co ==> e ; if co is a reflexive coercion" ] .+ Shallow .+ Bash
    , external "cast-elim-sym" (promoteExprR castElimSym :: RewriteH Core)
        [ "removes pairs of symmetric casts" ]                .+ Shallow .+ Bash
    , external "cast-elim-sym-plus" (promoteExprR castElimSymPlus :: RewriteH Core)
        [ "removes pairs of symmetric casts possibly separated by let or case forms" ] .+ Deep .+ TODO
    , external "cast-float-app" (promoteExprR castFloatApp :: RewriteH Core)
        [ "(cast e (c1 -> c2)) x ==> cast (e (cast x (sym c1))) c2" ] .+ Shallow
    , external "cast-elim-unsafe" (promoteExprR castElimUnsafe :: RewriteH Core)
        [ "removes casts regardless of whether it is safe to do so" ] .+ Shallow .+ Experiment .+ Unsafe .+ TODO
    ]

------------------------------------------------------------------------------

castElim :: MonadCatch m => Rewrite c m CoreExpr
castElim = setFailMsg "Cast elimination failed: " $
           castElimRefl <+ castElimSym

castElimRefl :: MonadCatch m => Rewrite c m CoreExpr
castElimRefl = prefixFailMsg "Reflexive cast elimination failed: " $
               withPatFailMsg (wrongExprForm "Cast e co") $
    do Cast e co <- idR
       Pair a b <- return $ coercionKind co
       guardMsg (eqType a b) "not a reflexive coercion."
       return e

castElimSym :: MonadCatch m => Rewrite c m CoreExpr
castElimSym = prefixFailMsg "Symmetric cast elimination failed: " $
              withPatFailMsg (wrongExprForm "Cast (Cast e co1) co2") $
    do Cast (Cast e co1) co2 <- idR
       let Pair a b   = coercionKind co1
           Pair b' a' = coercionKind co2
       guardMsg (eqType a a' && eqType b b') "coercions are not symmetric."
       return e

castFloatApp :: MonadCatch m => Rewrite c m CoreExpr
castFloatApp = prefixFailMsg "Cast float from application failed: " $
               withPatFailMsg (wrongExprForm "App (Cast e1 co) e2") $
    do App (Cast e1 co) e2 <- idR
       case co of
            TyConAppCo t [c1, c2] -> do
                True <- return (isFunTyCon t)
                return $ Cast (App e1 (Cast e2 (SymCo c1))) c2
            ForAllCo t c2 -> do
                Type x' <- return e2
                return (Cast (App e1 e2) (Coercion.substCo (Coercion.extendTvSubst emptyCvSubst t x') c2))
            _ -> fail "castFloatApp"

-- TODO: revisit
castElimSymPlus :: (ExtendPath c Crumb, AddBindings c, Monad m) => Rewrite c m CoreExpr
castElimSymPlus = castT idR idR (flip go) >>> joinT
  where
      go :: Monad m => Coercion -> CoreExpr -> m CoreExpr
      go _  (Var _) = fail "no symmetric casts found"
      go _  (Lit _) = fail "no symmetric casts found"
      go _  (App _ _) = fail "app unimplemented" {- focus [0] (go c1 (add arg)) -}
      go c1 (Lam x body)
        | Just (con, [arg, res]) <- splitTyConAppCo_maybe c1
        , con == funTyCon
        , Pair arg1 arg2 <- coercionKind arg
        , arg1 `eqType` arg2 = do
            body' <- go res body
            return (Lam x body')
        | otherwise = fail "lam unimplemented" {-focus [0] (go c1 (drop arg))-}
      go c1 (Let bs body) = do body' <- go c1 body
                               return (Let bs body')
      go c1 (Case scr x _ alts) = do alts' <- sequence [liftM ((,,) c a) (go c1 b) | (c,a,b) <- alts]
                                     let t' = exprType (case head alts' of (_,_,b) -> b)
                                     return (Case scr x t' alts')
      go c1 (Cast e c2) = if sym c1 c2 then return e else fail "no symmetric casts found"
      go _  (Tick{}) = fail "unexpected tick"
      go _  (Type{}) = fail "unexpected type"
      go _  (Coercion{}) = fail "unexpected coercion"

      sym :: Coercion -> Coercion -> Bool
      sym c1 c2
        | Pair c11 c12 <- coercionKind c1,
          Pair c21 c22 <- coercionKind c2,
          c11 `eqType` c22, c21 `eqType` c12 = True
        | otherwise = False
      --sym (SymCo c1) c2 = geq c1 c2
      --sym c1 (SymCo c2) = geq c1 c2
      --sym _ _ = False


castElimUnsafe :: (ExtendPath c Crumb, Monad m) => Rewrite c m CoreExpr
castElimUnsafe = castT idR idR const

