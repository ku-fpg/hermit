{-# LANGUAGE TupleSections, FlexibleContexts #-}
module Language.HERMIT.Primitive.Inline
         ( -- * Inlining
           externals
         , getUnfolding
         , inline
         , inlineName
         , inlineScrutinee
         , inlineCaseBinder
         , inlineTargets
         )

where

import GhcPlugins
import TcType (tcSplitDFunTy)

import Control.Arrow

import Language.HERMIT.Context
import Language.HERMIT.Core
import Language.HERMIT.External
import Language.HERMIT.GHC
import Language.HERMIT.Kure
import Language.HERMIT.Monad

import Language.HERMIT.Primitive.Common
import Language.HERMIT.Primitive.GHC hiding (externals)

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax (showName)

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
                [ "Inline if this variable is a case binder." ].+ Eval .+ Deep .+ Bash .+ TODO
            ]

------------------------------------------------------------------------

-- | If the current variable matches the given name, then inline it.
inlineName :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => TH.Name -> Rewrite c HermitM CoreExpr
inlineName nm = prefixFailMsg ("inline '" ++ showName nm ++ " failed: ") $
                withPatFailMsg (wrongExprForm "Var v") $
   do Var v <- idR
      guardMsg (cmpTHName2Var nm v) $ " does not match " ++ var2String v ++ "."
      inline

-- | Inline the current variable.
inline :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
inline = configurableInline False False

-- | Inline the current variable, using the scrutinee rather than the case alternative if it is a case wild-card binder.
inlineScrutinee :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
inlineScrutinee = configurableInline True False

-- | If the current variable is a case wild-card binder, then inline it.
inlineCaseBinder :: (ExtendPath c Crumb, AddBindings c, ReadBindings c) => Rewrite c HermitM CoreExpr
inlineCaseBinder = configurableInline False True

-- | The implementation of inline, an important transformation.
-- This *only* works on a Var of the given name. It can trivially
-- be prompted to more general cases.
configurableInline :: (ExtendPath c Crumb, AddBindings c, ReadBindings c)
                   => Bool -- ^ Inline the scrutinee instead of the patten match (for case binders).
                   -> Bool -- ^ Only inline if this variable is a case binder.
                   -> Rewrite c HermitM CoreExpr
configurableInline scrutinee caseBinderOnly =
   prefixFailMsg "Inline failed: " $
   withPatFailMsg (wrongExprForm "Var v") $
   do (c, Var v) <- exposeT
      (e,d) <- constT $ getUnfolding scrutinee caseBinderOnly v c
      return e >>> (setFailMsg "values in inlined expression have been rebound." $
                    accepterR (extractT $ ensureDepth d))


-- | Ensure all the free variables in an expression were bound above a given depth.
-- Assumes minimum depth is 0.
ensureDepth :: (ExtendPath c Crumb, AddBindings c, ReadBindings c, MonadCatch m) => Int -> Translate c m Core Bool
ensureDepth d = do
    frees <- promoteT freeVarsT
    ds <- collectT $ promoteExprT $ varT $ translate $ \ c i -> return $ if i `elem` frees
                                                                          then maybe (i,0) (\ b -> (i, fst b)) (lookupHermitBinding i c)
                                                                          else (i,0)
    return $ all (toSnd (<= d)) ds

getUnfolding :: ReadBindings c
             => Bool -- ^ Get the scrutinee instead of the patten match (for case binders).
             -> Bool -- ^ Only succeed if this variable is a case binder.
             -> Id -> c -> HermitM (CoreExpr, Int)
getUnfolding scrutinee caseBinderOnly i c =
    case lookupHermitBinding i c of
        Nothing -> if caseBinderOnly
                   then fail "not a case binder"
                   else case unfoldingInfo (idInfo i) of
                            CoreUnfolding { uf_tmpl = uft } -> return (uft, 0)
                            DFunUnfolding _arity dc args    -> dFunExpr dc args (idType i) >>= return . (,0)
                            _                               -> fail $ "cannot find unfolding in Env or IdInfo."
        Just (depth,b) -> case b of
                            CASEWILD s alt -> return $ if scrutinee
                                                        then (s, depth)
                                                        else let tys = tyConAppArgs (idType i)
                                                              in either (,depth) (,depth+1) (alt2Exp s tys alt)
                            _              -> if caseBinderOnly
                                               then fail "not a case binder."
                                               else case hermitBindingSiteExpr b of
                                                      Just e  -> return (e, depth)
                                                      Nothing -> fail $ "variable is not bound to an expression."

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

------------------------------------------------------------------------
