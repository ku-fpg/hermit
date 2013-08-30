{-# LANGUAGE CPP, TupleSections, FlexibleContexts #-}
module HERMIT.Primitive.Inline
         ( -- * Inlining
           externals
         , InlineConfig(..)
         , CaseBinderInlineOption(..)
         , getUnfoldingT
         , inlineR
         , inlineNameR
         , inlineCaseScrutineeR
         , inlineCaseAlternativeR
         , configurableInlineR
         , inlineAllR
         , inlineTargetsT
         )

where

import GhcPlugins
#if __GLASGOW_HASKELL__ > 706
#else
import TcType (tcSplitDFunTy)
#endif

import Control.Arrow
import Control.Applicative

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad

import HERMIT.Primitive.Common
import HERMIT.Primitive.GHC hiding (externals)

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------

-- | 'External's for inlining variables.
externals :: [External]
externals =
            [ external "inline" (promoteExprR inlineR :: RewriteH Core)
                [ "(Var v) ==> <defn of v>" ].+ Eval .+ Deep .+ TODO
            , external "inline" (promoteExprR . inlineNameR :: TH.Name -> RewriteH Core)
                [ "Given a specific v, (Var v) ==> <defn of v>" ].+ Eval .+ Deep
            , external "inline-case-scrutinee" (promoteExprR inlineCaseScrutineeR :: RewriteH Core)
                [ "if v is a case binder, replace (Var v) with the bound case scrutinee." ] .+ Eval .+ Deep
            , external "inline-case-alternative" (promoteExprR inlineCaseAlternativeR :: RewriteH Core)
                [ "if v is a case binder, replace (Var v) with the bound case-alternative pattern." ] .+ Eval .+ Deep .+ Unsafe
            , external "inline-all" (inlineAllR :: [TH.Name] -> RewriteH Core)
                [ "Recursively inline all occurrences of the given names, in a bottom-up manner." ] .+ Deep
            ]

------------------------------------------------------------------------

-- | Recursively inline all occurrences of the given names.
inlineAllR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => [TH.Name] -> Rewrite c HermitM Core
inlineAllR []  = fail "inline-all failed: no names given."
inlineAllR nms = innermostR (promoteExprR $ orR $ map inlineNameR nms)

------------------------------------------------------------------------

-- extend these data types as needed if other inlining behaviour becomes desireable
data CaseBinderInlineOption = Scrutinee | Alternative deriving (Eq, Show)
data InlineConfig           = CaseBinderOnly CaseBinderInlineOption | AllBinders deriving (Eq, Show)

-- | If the current variable matches the given name, then inline it.
inlineNameR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => TH.Name -> Rewrite c HermitM CoreExpr
inlineNameR nm = configurableInlineR AllBinders (arr $ cmpTHName2Var nm)

-- | Inline the current variable.
inlineR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
inlineR = configurableInlineR AllBinders (return True)

-- | Inline the current identifier if it is a case binder, using the scrutinee rather than the case-alternative pattern.
inlineCaseScrutineeR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
inlineCaseScrutineeR = configurableInlineR (CaseBinderOnly Scrutinee) (return True)

-- | Inline the current identifier if is a case binder, using the case-alternative pattern rather than the scrutinee.
inlineCaseAlternativeR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
inlineCaseAlternativeR = configurableInlineR (CaseBinderOnly Alternative) (return True)

-- | The implementation of inline, an important transformation.
-- This *only* works if the current expression has the form @Var v@ (it does not traverse the expression).
-- It can trivially be prompted to more general cases using traversal strategies.
configurableInlineR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c)
                    => InlineConfig
                    -> (Translate c HermitM Id Bool) -- ^ Only inline identifiers that satisfy this predicate.
                    -> Rewrite c HermitM CoreExpr
configurableInlineR config p =
   prefixFailMsg "Inline failed: " $
   do b <- varT p
      guardMsg b "identifier does not satisfy predicate."
      (e,d) <- varT (getUnfoldingT config)
      return e >>> (setFailMsg "values in inlined expression have been rebound." $
                    accepterR (extractT $ ensureDepthT d))


-- TODO: The comment says "above a given depth", but the code checks the depths are <= a given depth.
-- Also, I note that the code used to return 0 for free variables not in the HERMIT context.
-- I removed it, as 0 <= d was always true (as we assume non-negative d).  However, if the <= should be >=, it will need reinstating.

-- | Ensure all the free variables in an expression were bound above a given depth.
-- Assumes minimum depth is 0.
ensureDepthT :: (ExtendPath c Crumb, AddBindings c, ReadBindings c, MonadCatch m) => BindingDepth -> Translate c m Core Bool
ensureDepthT d = do
    frees <- promoteT exprFreeVarsT
    ds <- collectT $ promoteExprT $ varT $ do i <- idR
                                              guardM (i `elemVarSet` frees)
                                              varBindingDepthT i
    return $ all (<= d) ds

getUnfoldingT :: ReadBindings c
              => InlineConfig
              -> Translate c HermitM Id (CoreExpr, BindingDepth)
getUnfoldingT config = translate $ \ c i ->
    case lookupHermitBinding i c of
      Nothing -> case config of
                   CaseBinderOnly _ -> fail "not a case binder."
                   AllBinders       -> case unfoldingInfo (idInfo i) of
                                         CoreUnfolding { uf_tmpl = uft } -> return (uft, 0)
#if __GLASGOW_HASKELL__ > 706
                                         dunf@(DFunUnfolding {})         -> (,0) <$> dFunExpr dunf
#else
                                         DFunUnfolding _arity dc args    -> (,0) <$> dFunExpr dc args (idType i)
#endif
                                         _                               -> fail $ "cannot find unfolding in Env or IdInfo."
      Just (depth,b) -> case b of
                          CASEWILD s alt -> let tys             = tyConAppArgs (idType i)
                                                altExprDepthM   = (,depth+1) <$> alt2Exp tys alt
                                                scrutExprDepthM = return (s, depth)
                                             in case config of
                                                  CaseBinderOnly Scrutinee   -> scrutExprDepthM
                                                  CaseBinderOnly Alternative -> altExprDepthM
                                                  AllBinders                 -> altExprDepthM <+ scrutExprDepthM
                          _              -> case config of
                                              CaseBinderOnly _ -> fail "not a case binder."
                                              AllBinders       -> (,depth) <$> liftKureM (hermitBindingSiteExpr b)

-- | Convert lhs of case alternative to a constructor application expression,
--   failing in the case of the DEFAULT alternative.
--   Accepts a list of types to apply to the constructor before the value args.
--
-- > data T a b = C a b Int
--
-- Pseudocode:
--
-- > alt2Exp (...) [a,b] (C, [x,y,z]) ==> C a b (x::a) (y::b) (z::Int)
--
alt2Exp :: Monad m => [Type] -> (AltCon,[Var]) -> m CoreExpr
alt2Exp _   (DEFAULT   , _ ) = fail "DEFAULT alternative cannot be converted to an expression."
alt2Exp _   (LitAlt l  , _ ) = return $ Lit l
alt2Exp tys (DataAlt dc, vs) = return $ mkCoreConApps dc (map Type tys ++ map (varToCoreExpr . zapVarOccInfo) vs)

-- | Get list of possible inline targets. Used by shell for completion.
inlineTargetsT :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Translate c HermitM Core [String]
inlineTargetsT = collectT $ promoteT $ whenM (testM inlineR) (varT $ arr var2String)

-- | Build a CoreExpr for a DFunUnfolding
#if __GLASGOW_HASKELL__ > 706
{-
data Unfolding
  = ...
  | DFunUnfolding {     -- The Unfolding of a DFunId
                -- See Note [DFun unfoldings]
                --     df = /\a1..am. \d1..dn. MkD t1 .. tk
                        --                                 (op1 a1..am d1..dn)
                    --                                 (op2 a1..am d1..dn)
        df_bndrs :: [Var],      -- The bound variables [a1..m],[d1..dn]
        df_con   :: DataCon,    -- The dictionary data constructor (never a newtype datacon)
        df_args  :: [CoreExpr]  -- Args of the data con: types, superclasses and methods,
    }                           -- in positional order
-}
dFunExpr :: Unfolding -> HermitM CoreExpr
-- TODO: is this correct?
dFunExpr dunf@(DFunUnfolding {}) = return $ trace "dFunExpr" $ mkCoreConApps (df_con dunf) (df_args dunf)
dFunExpr _ = fail "dFunExpr: not a DFunUnfolding"
#else
dFunExpr :: DataCon -> [DFunArg CoreExpr] -> Type -> HermitM CoreExpr
dFunExpr dc args ty = do
    let (_, _, _, tcArgs) = tcSplitDFunTy ty
        (forallTvs, ty')  = splitForAllTys ty
        (argTys, _resTy)  = splitFunTys ty'

    ids <- mapM (uncurry newIdH) $ zip [ [ch] | ch <- cycle ['a'..'z'] ] argTys
    vars <- mapM (cloneVarH id) forallTvs

    let allVars = varsToCoreExprs $ vars ++ ids

        mkArg (DFunLamArg i) = allVars !! i
        mkArg (DFunPolyArg e) = mkCoreApps e allVars

    return $ mkCoreConApps dc $ map Type tcArgs ++ map mkArg args
#endif

------------------------------------------------------------------------
