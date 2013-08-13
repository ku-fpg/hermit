{-# LANGUAGE CPP, TupleSections, FlexibleContexts, ScopedTypeVariables #-}
module Language.HERMIT.Primitive.Inline
         ( -- * Inlining
           externals
         , getUnfoldingT
         , inline
         , inlineName
         , inlineScrutinee
         , inlineCaseBinder
         , caseInlineScrutineeR
         , inlineAll
         , inlineTargets
         )

where

import GhcPlugins
#if __GLASGOW_HASKELL__ > 706
#else
import TcType (tcSplitDFunTy)
#endif

import Control.Arrow
import Control.Applicative

import Data.Set (member)

import Language.HERMIT.Context
import Language.HERMIT.Core
import Language.HERMIT.External
import Language.HERMIT.GHC
import Language.HERMIT.Kure
import Language.HERMIT.Monad

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.GHC hiding (externals)

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------

-- | 'External's for inlining variables.
externals :: [External]
externals =
            [ external "inline" (promoteExprR inline :: RewriteH Core)
                [ "(Var n) ==> <defn of n>, fails otherwise" ].+ Eval .+ Deep .+ TODO
            , external "inline-scrutinee" (promoteExprR inlineScrutinee :: RewriteH Core)
                [ "(Var n) ==> <defn of n>, fails otherwise"
                , "In the case of case binders, replaces with scrutinee expression, "
                , "rather than constructor or literal." ].+ Eval .+ Deep .+ TODO
            , external "inline" (promoteExprR . inlineName :: TH.Name -> RewriteH Core)
                [ "Restrict inlining to a given name" ].+ Eval .+ Deep .+ TODO
            , external "inline-case-binder" (promoteExprR inlineCaseBinder :: RewriteH Core)
                [ "Inline if this variable is a case binder." ].+ Eval .+ Deep {- this causes a Dead Id core list error if in bash .+ Bash -} .+ TODO
                -- Neil:  I would really like to get inline-case-binder back in "bash".  Maybe when "auto-core-lint" is switched on, we could run the occurence analyser to update id-info?
            , external "inline-all" (inlineAll :: [TH.Name] -> RewriteH Core)
                [ "Recursively inline all occurrences of the given names, in a bottom-up manner." ] .+ Deep
            ]

------------------------------------------------------------------------

-- | Recursively inline all occurrences of the given names.
inlineAll :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => [TH.Name] -> Rewrite c HermitM Core
inlineAll []  = fail "inline-all failed: no names given."
inlineAll nms = innermostR (promoteExprR $ orR $ map inlineName nms)

------------------------------------------------------------------------

-- | If the current variable matches the given name, then inline it.
inlineName :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => TH.Name -> Rewrite c HermitM CoreExpr
inlineName nm = configurableInline False False (arr $ cmpTHName2Var nm) Nothing

-- | Inline the current variable.
inline :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
inline = configurableInline False False (return True) Nothing

-- | Inline the current variable, using the scrutinee rather than the case alternative if it is a case wild-card binder.
inlineScrutinee :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
inlineScrutinee = configurableInline True False (return True) Nothing

-- | If the current variable is a case wild-card binder, then inline it.
inlineCaseBinder :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
inlineCaseBinder = configurableInline False True (return True) Nothing

-- | Inline the case wildcard binder as the case scrutinee everywhere in the case alternatives.
caseInlineScrutineeR :: forall c. (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
caseInlineScrutineeR = prefixFailMsg "case-inline-scrutinee failed: " $
                       do w <- caseWildIdT
                          caseAllR idR idR idR $ \ _ -> do depth <- varBindingDepthT w
                                                           extractR $ anybuR (promoteExprR (configurableInline True True (arr (== w)) (Just depth)) :: Rewrite c HermitM Core)


-- | The implementation of inline, an important transformation.
-- This *only* works on a Var of the given name. It can trivially
-- be prompted to more general cases.
configurableInline :: (ExtendPath c Crumb, AddBindings c, ReadBindings c)
                   => Bool -- ^ Inline the scrutinee instead of the patten match (for case binders).
                   -> Bool -- ^ Only inline if this variable is a case binder.
                   -> (Translate c HermitM Id Bool) -- ^ Only inline identifiers that satisfy this predicate.
                   -> Maybe BindingDepth -- ^ Ensure the binding has a specific depth (useful if there are multiple (shadowing) occurrences of an identifier).
                   -> Rewrite c HermitM CoreExpr
configurableInline scrutinee caseBinderOnly p md =
   prefixFailMsg "Inline failed: " $
   withPatFailMsg (wrongExprForm "Var v") $
   do b <- varT p
      guardMsg b "identifier does not satisfy predicate."
      (e,d) <- varT (getUnfoldingT scrutinee caseBinderOnly md)
      return e >>> (setFailMsg "values in inlined expression have been rebound." $
                    accepterR (extractT $ ensureDepth d))


-- TODO: The comment says "above a given depth", but the code checks the depths are <= a given depth.
-- Also, I note that the code used to return 0 for free variables not in the HERMIT context.
-- I removed it, as 0 <= d was always true (as we assume non-negative d).  However, if the <= should be >=, it will need reinstating.

-- | Ensure all the free variables in an expression were bound above a given depth.
-- Assumes minimum depth is 0.
ensureDepth :: (ExtendPath c Crumb, AddBindings c, ReadBindings c, MonadCatch m) => BindingDepth -> Translate c m Core Bool
ensureDepth d = do
    frees <- promoteT freeVarsT
    ds <- collectT $ promoteExprT $ varT $ do i <- idR
                                              guardM (i `member` frees)
                                              varBindingDepthT i
    return $ all (<= d) ds

getUnfoldingT :: ReadBindings c
              => Bool -- ^ Get the scrutinee instead of the patten match (for case binders).
              -> Bool -- ^ Only succeed if this variable is a case binder.
              -> Maybe BindingDepth -- ^ Ensure the binding has a specific depth (useful if there are multiple (shadowing) occurrences of an identifier)
              -> Translate c HermitM Id (CoreExpr, BindingDepth)
getUnfoldingT scrutinee caseBinderOnly md =
   do (c, i) <- exposeT
      case lookupHermitBinding i c of
        Nothing -> if caseBinderOnly
                     then fail "not a case binder"
                     else -- TODO: maybe check for depth 0 here?  But if there's a shadow, we'll be in the other branch anyway.  Maybe we should enter this branch if the depth check fails?
                          case unfoldingInfo (idInfo i) of
                               CoreUnfolding { uf_tmpl = uft } -> return (uft, 0)
#if __GLASGOW_HASKELL__ > 706
                               dunf@(DFunUnfolding {})         -> constT ((,0) <$> dFunExpr dunf)
#else
                               DFunUnfolding _arity dc args    -> constT ((,0) <$> dFunExpr dc args (idType i))
#endif
                               _                               -> fail $ "cannot find unfolding in Env or IdInfo."
        Just (depth,b) -> do guardMsg (maybe True (== depth) md) "foldVar failed: this is a shadowing occurrence of the identifier."
                             case b of
                               CASEWILD s alt -> return $ if scrutinee
                                                           then (s, depth)
                                                           else let tys = tyConAppArgs (idType i)
                                                                 in either (,depth) (,depth+1) (alt2Exp s tys alt)
                               _              -> if caseBinderOnly
                                                  then fail "not a case binder."
                                                  else (,depth) <$> liftKureM (hermitBindingSiteExpr b)

-- | Convert lhs of case alternative to a constructor application expression,
--   or a default expression in the case of the DEFAULT alternative.
--   Accepts a list of types to apply to the constructor before the value args.
--
-- > data T a b = C a b Int
--
-- Pseudocode:
--
-- > alt2Exp (...) [a,b] (C, [x,y,z]) ==> C a b (x::a) (y::b) (z::Int)
--
-- The 'Either' denotes whether we picked the default (scrutinee) or built an expression.
-- This matters for the depth check.
alt2Exp :: CoreExpr -> [Type] -> (AltCon,[Id]) -> Either CoreExpr CoreExpr
alt2Exp d _   (DEFAULT   , _ ) = Left d
alt2Exp _ _   (LitAlt l  , _ ) = Right $ Lit l
alt2Exp _ tys (DataAlt dc, as) = Right $ mkCoreConApps dc (map Type tys ++ map varToCoreExpr as)

-- | Get list of possible inline targets. Used by shell for completion.
inlineTargets :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Translate c HermitM Core [String]
inlineTargets = collectT $ promoteT $ whenM (testM inline) (varT $ arr var2String)

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
