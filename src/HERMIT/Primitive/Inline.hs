{-# LANGUAGE CPP, TupleSections, FlexibleContexts, ScopedTypeVariables #-}
module HERMIT.Primitive.Inline
         ( -- * Inlining
           externals
         , InlineConfig(..)
         , CaseBinderInlineOption(..)
         , getUnfoldingT
         , inlineR
         , inlineNameR
         , inlineNamesR
         , inlineCaseScrutineeR
         , inlineCaseAlternativeR
         , configurableInlineR
         , inlineTargetsT
         )

where

#if __GLASGOW_HASKELL__ > 706
#else
import TcType (tcSplitDFunTy)
#endif

import Control.Arrow
import Control.Applicative
import Control.Monad

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad

import HERMIT.Primitive.Common

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------

-- | 'External's for inlining variables.
externals :: [External]
externals =
            [ external "inline" (promoteExprR inlineR :: RewriteH Core)
                [ "(Var v) ==> <defn of v>" ].+ Eval .+ Deep
            , external "inline" (promoteExprR . inlineNameR :: TH.Name -> RewriteH Core)
                [ "Given a specific v, (Var v) ==> <defn of v>" ] .+ Eval .+ Deep
            , external "inline" (promoteExprR . inlineNamesR :: [TH.Name] -> RewriteH Core)
                [ "If the current variable matches any of the given names, then inline it." ] .+ Eval .+ Deep
            , external "inline-case-scrutinee" (promoteExprR inlineCaseScrutineeR :: RewriteH Core)
                [ "if v is a case binder, replace (Var v) with the bound case scrutinee." ] .+ Eval .+ Deep
            , external "inline-case-alternative" (promoteExprR inlineCaseAlternativeR :: RewriteH Core)
                [ "if v is a case binder, replace (Var v) with the bound case-alternative pattern." ] .+ Eval .+ Deep .+ Unsafe
            ]

------------------------------------------------------------------------

-- extend these data types as needed if other inlining behaviour becomes desireable
data CaseBinderInlineOption = Scrutinee | Alternative deriving (Eq, Show)
data InlineConfig           = CaseBinderOnly CaseBinderInlineOption | AllBinders deriving (Eq, Show)

-- | If the current variable matches the given name, then inline it.
inlineNameR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => TH.Name -> Rewrite c HermitM CoreExpr
inlineNameR nm = configurableInlineR AllBinders (arr $ cmpTHName2Var nm)

-- | If the current variable matches any of the given names, then inline it.
inlineNamesR :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => [TH.Name] -> Rewrite c HermitM CoreExpr
inlineNamesR []  = fail "inline-names failed: no names given."
inlineNamesR nms = configurableInlineR AllBinders (arr $ \ v -> any (flip cmpTHName2Var v) nms)

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
      (e,uncaptured) <- varT (getUnfoldingT config)
      setFailMsg "values in inlined expression have been rebound."
        (return e >>> accepterR (ensureDepthT uncaptured))


-- NOTE: When inlining, we have to take care to avoid variable capture.
--       Our approach is to track the binding depth of the inlined identifier.
--       After inlining, we then resolve all names in the inlined expression, and require that they were all bound prior to (i.e. lower numbered depth) the binding we inlined.
--       The precise depth check varies between binding types as follows (where d is the depth of the inlined binder):
--
--         Binder                Safe to Inline
--         global-id             (<= 0)
--         letnonrec             (< d)
--         letrec                (<= d)
--         case-wild-scrutinee   (< d)
--         case-wild-alt         (<= d+1)
--         self-rec-def          NA
--         lam                   NA
--         case-alt              NA


-- | Ensure all the free variables in an expression were bound above a given depth.
-- Assumes minimum depth is 0.
ensureDepthT :: forall c m. (ExtendPath c Crumb, AddBindings c, ReadBindings c, MonadCatch m) => (BindingDepth -> Bool) -> Translate c m CoreExpr Bool
ensureDepthT uncaptured =
  do frees <- arr localFreeVarsExpr
     let collectDepthsT :: Translate c m Core [BindingDepth]
         collectDepthsT = collectT $ promoteExprT $ varT (acceptR (`elemVarSet` frees) >>> readerT varBindingDepthT)
     all uncaptured `liftM` extractT collectDepthsT

-- | Return the unfolding of an identifier, and a predicate over the binding depths of all variables within that unfolding to determine if they have been captured in their new location.
getUnfoldingT :: ReadBindings c
              => InlineConfig
              -> Translate c HermitM Id (CoreExpr, BindingDepth -> Bool)
getUnfoldingT config = translate $ \ c i ->
    case lookupHermitBinding i c of
      Nothing -> do requireAllBinders config
                    let uncaptured = (<= 0) -- i.e. is global
                    case unfoldingInfo (idInfo i) of
                      CoreUnfolding { uf_tmpl = uft } -> return (uft, uncaptured)
#if __GLASGOW_HASKELL__ > 706
                      dunf@(DFunUnfolding {})         -> (,uncaptured) <$> dFunExpr dunf
#else
                      DFunUnfolding _arity dc args    -> (,uncaptured) <$> dFunExpr dc args (idType i)
#endif
                      _                               -> fail $ "cannot find unfolding in Env or IdInfo."
      Just (depth,b) -> case b of
                          CASEWILD s alt -> let tys             = tyConAppArgs (idType i)
                                                altExprDepthM   = (, (<= depth+1)) <$> alt2Exp tys alt
                                                scrutExprDepthM = return (s, (< depth))
                                             in case config of
                                                  CaseBinderOnly Scrutinee   -> scrutExprDepthM
                                                  CaseBinderOnly Alternative -> altExprDepthM
                                                  AllBinders                 -> altExprDepthM <+ scrutExprDepthM

                          NONREC e       -> do requireAllBinders config
                                               return (e, (< depth))

                          REC e          -> do requireAllBinders config
                                               return (e, (<= depth))

                          _              -> fail "variable is not bound to an expression."
  where
    requireAllBinders :: Monad m => InlineConfig -> m ()
    requireAllBinders AllBinders         = return ()
    requireAllBinders (CaseBinderOnly _) = fail "not a case binder."

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
