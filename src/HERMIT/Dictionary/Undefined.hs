{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}

module HERMIT.Dictionary.Undefined
    ( -- * Working with Undefined Values
      -- | Note that many of these operations require 'GHC.Err.undefined' to be explicitly imported if it is not used in the source file.
      externals
    , buildStrictnessLemmaT
    , verifyStrictT
    , applyToUndefinedT
    , mkUndefinedValT
    , isUndefinedValT
    , replaceCurrentExprWithUndefinedR
    , replaceIdWithUndefinedR
    , replaceIdWithUndefined 
    , errorToUndefinedR
    , undefinedExprR
    , undefinedAppR
    , undefinedLamR
    , undefinedLetR
    , undefinedCaseScrutineeR
    , undefinedCaseAltsR
    , undefinedCaseR
    , undefinedCastR
    , undefinedTickR
    ) where

import Control.Monad ((>=>), liftM)
import Control.Monad.IO.Class
import Data.Monoid
import Data.String (fromString)

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC hiding ((<>))
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Monad
import HERMIT.Name

import HERMIT.Dictionary.Common
import HERMIT.Dictionary.GHC (substR)
import HERMIT.Dictionary.Reasoning hiding (externals)

import HERMIT.Exception

import Control.Monad.Fail (MonadFail)

------------------------------------------------------------------------

externals :: [External]
externals = map (.+ Strictness)
    [ external "replace-current-expr-with-undefined" (promoteExprR replaceCurrentExprWithUndefinedR :: RewriteH LCore)
        [ "Set the current expression to \"undefined\"."
        ] .+ Shallow .+ Context .+ Unsafe
    , external "replace-id-with-undefined" (promoteCoreR . replaceIdWithUndefined :: HermitName -> RewriteH LCore)
        [ "Replace the specified identifier with \"undefined\"."
        ] .+ Deep .+ Context .+ Unsafe
    , external "error-to-undefined" (promoteExprR errorToUndefinedR :: RewriteH LCore)
        [ "error ty string  ==>  undefined ty"
        ] .+ Shallow .+ Context
    , external "is-undefined-val" (promoteExprT isUndefinedValT :: TransformH LCore ())
        [ "Succeed if the current expression is an undefined value."
        ] .+ Shallow .+ Context .+ Predicate
    , external "undefined-expr" (promoteExprR undefinedExprR :: RewriteH LCore)
        [ "undefined-app <+ undefined-lam <+ undefined-let <+ undefined-cast <+ undefined-tick <+ undefined-case"
        ] .+ Eval .+ Shallow .+ Context
    , external "undefined-app" (promoteExprR undefinedAppR :: RewriteH LCore)
        [ "(undefined ty1) e  ==>  undefined ty2"
        ] .+ Eval .+ Shallow .+ Context
    , external "undefined-lam" (promoteExprR undefinedLamR :: RewriteH LCore)
        [ "(\\ v -> undefined ty1)  ==>  undefined ty2   (where v is not a 'TyVar')"
        ] .+ Eval .+ Shallow .+ Context
    , external "undefined-let" (promoteExprR undefinedLetR :: RewriteH LCore)
        [ "let bds in (undefined ty)  ==>  undefined ty"
        ] .+ Eval .+ Shallow .+ Context
    , external "undefined-case" (promoteExprR undefinedCaseR :: RewriteH LCore)
        [ "case (undefined ty) of alts  ==>  undefined ty"
        , "OR"
        , "case e of {pat_1 -> undefined ty ; pat_2 -> undefined ty ; ... ; pat_n -> undefined ty} ==> undefined ty"
        ] .+ Eval .+ Shallow .+ Context
    , external "undefined-cast" (promoteExprR undefinedCastR :: RewriteH LCore)
        [ "Cast (undefined ty1) co  ==>  undefined ty2"
        ] .+ Eval .+ Shallow .+ Context
    , external "undefined-tick" (promoteExprR undefinedTickR :: RewriteH LCore)
        [ "Tick tick (undefined ty1)  ==>  undefined ty1"
        ] .+ Eval .+ Shallow .+ Context
    ]

------------------------------------------------------------------------

undefinedLocation :: HermitName
undefinedLocation = fromString "GHC.Err.undefined"

findUndefinedIdT :: (BoundVars c, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Transform c m a Id
findUndefinedIdT = findIdT undefinedLocation

-- | Check if the current expression is an undefined value.
isUndefinedValT :: (MonadFail m, BoundVars c, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Transform c m CoreExpr ()
isUndefinedValT = prefixFailMsg "not an undefined value: " $
                  withPatFailExc (HException (wrongExprForm "App (Var undefined) (Type ty)")) $
                  do App (Var un) (Type _) <- idR
                     un' <- findUndefinedIdT
                     guardMsg (un == un') ("identifier is not " ++ show undefinedLocation)

------------------------------------------------------------------------

errorLocation :: HermitName
errorLocation = fromString "GHC.Err.error"

findErrorIdT :: (BoundVars c, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Transform c m a Id
findErrorIdT = findIdT errorLocation

-- | Check if the current expression is an undefined value.
isErrorValT :: (MonadFail m, BoundVars c, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Transform c m CoreExpr ()
isErrorValT = prefixFailMsg "not an error value: " $
              withPatFailExc (HException (wrongExprForm "App (App (Var error) (Type ty)) string")) $
              do App (App (Var er) (Type _)) _ <- idR
                 er' <- findErrorIdT
                 guardMsg (er == er') ("identifier is not " ++ show errorLocation)

------------------------------------------------------------------------

-- | error ty string ==> undefined ty
errorToUndefinedR :: (MonadFail m, BoundVars c, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Rewrite c m CoreExpr
errorToUndefinedR = prefixFailMsg "error-to-undefined failed: " (isErrorValT >> replaceCurrentExprWithUndefinedR)

------------------------------------------------------------------------

-- | Make an undefined value of the given type.
mkUndefinedValT :: (BoundVars c, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Type -> Transform c m a CoreExpr
mkUndefinedValT ty =
  do un <- findUndefinedIdT
     return $ App (varToCoreExpr un) (Type ty)

------------------------------------------------------------------------------------------------------

-- | Set the current expression to 'undefined'.
replaceCurrentExprWithUndefinedR :: (BoundVars c, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Rewrite c m CoreExpr
replaceCurrentExprWithUndefinedR = contextfreeT exprTypeM >>= mkUndefinedValT

-- | Replace all occurrences of the specified identifier with 'undefined'.
replaceIdWithUndefinedR :: (BoundVars c, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Id -> Rewrite c m Core
replaceIdWithUndefinedR i = mkUndefinedValT (idType i) >>= substR i

replaceIdWithUndefined :: (BoundVars c, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m)                        => HermitName -> Rewrite c m Core
replaceIdWithUndefined = findIdT >=> replaceIdWithUndefinedR

------------------------------------------------------------------------------------------------------

-- | undefinedExprR = undefinedAppR <+ undefinedLamR <+ undefinedLetR <+ undefinedCastR <+ undefinedTickR <+ undefinedCaseR
undefinedExprR :: (MonadFail m, AddBindings c, BoundVars c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Rewrite c m CoreExpr
undefinedExprR = setFailMsg "undefined-expr failed."
                   (undefinedAppR <+ undefinedLamR <+ undefinedLetR <+ undefinedCastR <+ undefinedTickR <+ undefinedCaseR)

------------------------------------------------------------------------------------------------------

-- | @(undefined ty1) e@ ==> @undefined ty2@
undefinedAppR :: (MonadFail m, BoundVars c, ExtendPath c Crumb, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Rewrite c m CoreExpr
undefinedAppR = prefixFailMsg "undefined-app failed: " $
                do appT isUndefinedValT successT (<>)
                   replaceCurrentExprWithUndefinedR

-- | @(\ v -> undefined ty1)@ ==> @undefined ty2@  (where v is not a 'TyVar')
undefinedLamR :: (MonadFail m, AddBindings c, BoundVars c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Rewrite c m CoreExpr
undefinedLamR = prefixFailMsg "undefined-lam failed: " $
                do lamT successT isUndefinedValT (<>)
                   replaceCurrentExprWithUndefinedR

-- | let bds in (undefined ty) ==> undefined ty
undefinedLetR :: (MonadFail m, AddBindings c, BoundVars c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Rewrite c m CoreExpr
undefinedLetR = prefixFailMsg "undefined-let failed: " $
                do letT successT isUndefinedValT (<>)
                   replaceCurrentExprWithUndefinedR

-- | Cast (undefined ty1) co ==> undefined ty2
undefinedCastR :: (MonadFail m, BoundVars c, ExtendPath c Crumb, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Rewrite c m CoreExpr
undefinedCastR = prefixFailMsg "undefined-cast failed: " $
                do castT isUndefinedValT successT (<>)
                   replaceCurrentExprWithUndefinedR

-- | Tick tick (undefined ty1) ==> undefined ty1
undefinedTickR :: (MonadFail m, BoundVars c, ExtendPath c Crumb, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Rewrite c m CoreExpr
undefinedTickR = prefixFailMsg "undefined-tick failed: " $
                do tickT successT isUndefinedValT (<>)
                   replaceCurrentExprWithUndefinedR

-- | undefinedCaseR = undefinedCaseScrutineeR <+ undefinedCaseAltsR
undefinedCaseR :: (MonadFail m, AddBindings c, BoundVars c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Rewrite c m CoreExpr
undefinedCaseR = setFailMsg "undefined-case failed" (undefinedCaseScrutineeR <+ undefinedCaseAltsR)

-- | case (undefined ty) of alts ==> undefined ty
undefinedCaseScrutineeR :: (MonadFail m, AddBindings c, BoundVars c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Rewrite c m CoreExpr
undefinedCaseScrutineeR = prefixFailMsg "undefined-case failed: " $
                 do caseT isUndefinedValT successT successT (const successT) (\ _ _ _ _ -> ())
                    replaceCurrentExprWithUndefinedR

-- | case e of {pat_1 -> undefined ty ; pat_2 -> undefined ty ; ... ; pat_n -> undefined ty} ==> undefined ty
undefinedCaseAltsR :: (MonadFail m, AddBindings c, BoundVars c, ExtendPath c Crumb, ReadPath c Crumb, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => Rewrite c m CoreExpr
undefinedCaseAltsR = prefixFailMsg "undefined-case-alts failed: " $
                     do caseAltT successT successT successT (const (successT,const successT,isUndefinedValT)) (\ _ _ _ _ -> ())
                        replaceCurrentExprWithUndefinedR

------------------------------------------------------------------------

-- | Verify that the given rewrite is a proof that the given expression is a strict function.
verifyStrictT :: (BoundVars c, MonadCatch m, HasHermitMEnv m, LiftCoreM m, MonadIO m, MonadThings m) => CoreExpr -> Rewrite c m CoreExpr -> Transform c m a ()
verifyStrictT f r = prefixFailMsg "strictness verification failed: " $
  do (_, argTy, resTy) <- constT (funExprArgResTypesM f)
     undefArg       <- mkUndefinedValT argTy
     rhs            <- mkUndefinedValT resTy
     let lhs = App f undefArg
     verifyEqualityLeftToRightT lhs rhs r

-- | Apply the given expression to undefined, at the proper type.
applyToUndefinedT :: (BoundVars c, LiftCoreM m, HasHermitMEnv m, MonadCatch m, MonadIO m, MonadThings m)
                  => CoreExpr -> Transform c m x CoreExpr
applyToUndefinedT f = do
    let (tvs, body) = collectTyBinders f
    (_,dom,_) <- splitFunTypeM (exprType body)
    undef <- mkUndefinedValT dom
#if __GLASGOW_HASKELL__ > 710
    return $ mkCoreLams tvs $ mkCoreApp (text "applyToUndefinedT") body undef
#else
    return $ mkCoreLams tvs $ mkCoreApp body undef
#endif

-- | Add a lemma for the strictness of a function.
-- Note: assumes added lemma has been used
buildStrictnessLemmaT :: ( MonadFail m, HasCoreRules c, LemmaContext c, ReadBindings c
                         , ReadPath c Crumb, LiftCoreM m, HasHermitMEnv m, HasLemmas m
                         , MonadCatch m, MonadIO m, MonadThings m)
                      => Used -> LemmaName -> CoreExpr -> Transform c m x ()
buildStrictnessLemmaT u nm f = do
    (tvs, lhs) <- liftM collectTyBinders $ applyToUndefinedT f
    rhs <- mkUndefinedValT (exprType lhs)
    verifyOrCreateT u nm (mkClause tvs lhs rhs)

------------------------------------------------------------------------
