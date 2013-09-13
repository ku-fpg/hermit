{-# LANGUAGE FlexibleContexts #-}
module HERMIT.Primitive.Undefined
    ( -- * Working with Undefined Values
      -- | Note that many of these operations require 'GHC.Err.undefined' to be explicitly imported if it is not used in the source file.
      externals
    , verifyStrictT
    , mkUndefinedValT
    , isUndefinedValT
    , replaceWithUndefinedR
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
    )
where

import Data.Monoid

import HERMIT.Context
import HERMIT.Core
import HERMIT.Kure
import HERMIT.GHC hiding ((<>))
import HERMIT.External

import HERMIT.Primitive.Common

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------

externals :: [External]
externals = map (.+ Unsafe)
    [ external "replace-with-undefined" (promoteExprR replaceWithUndefinedR :: RewriteH Core)
        [ "Set the current expression to \"undefined\"."
        ] .+ Shallow .+ Context .+ Unsafe
    , external "error-to-undefined" (promoteExprR errorToUndefinedR :: RewriteH Core)
        [ "error ty string  ==>  undefined ty"
        ] .+ Shallow .+ Context
    , external "is-undefined-val" (promoteExprT isUndefinedValT :: TranslateH Core ())
        [ "Succeed if the current expression is an undefined value."
        ] .+ Shallow .+ Context .+ Predicate
    , external "undefined-expr" (promoteExprR undefinedExprR :: RewriteH Core)
        [ "undefined-app <+ undefined-lam <+ undefined-let <+ undefined-cast <+ undefined-tick <+ undefined-case"
        ] .+ Eval .+ Shallow .+ Context
    , external "undefined-app" (promoteExprR undefinedAppR :: RewriteH Core)
        [ "(undefined ty1) e  ==>  undefined ty2"
        ] .+ Eval .+ Shallow .+ Context
    , external "undefined-lam" (promoteExprR undefinedLamR :: RewriteH Core)
        [ "(\\ v -> undefined ty1)  ==>  undefined ty2   (where v is not a 'TyVar')"
        ] .+ Eval .+ Shallow .+ Context
    , external "undefined-let" (promoteExprR undefinedLetR :: RewriteH Core)
        [ "let bds in (undefined ty)  ==>  undefined ty"
        ] .+ Eval .+ Shallow .+ Context
    , external "undefined-case" (promoteExprR undefinedCaseR :: RewriteH Core)
        [ "case (undefined ty) of alts  ==>  undefined ty"
        , "OR"
        , "case e of {pat_1 -> undefined ty ; pat_2 -> undefined ty ; ... ; pat_n -> undefined ty} ==> undefined ty"
        ] .+ Eval .+ Shallow .+ Context
    , external "undefined-cast" (promoteExprR undefinedCastR :: RewriteH Core)
        [ "Cast (undefined ty1) co  ==>  undefined ty2"
        ] .+ Eval .+ Shallow .+ Context
    , external "undefined-tick" (promoteExprR undefinedTickR :: RewriteH Core)
        [ "Tick tick (undefined ty1)  ==>  undefined ty1"
        ] .+ Eval .+ Shallow .+ Context
    ]

------------------------------------------------------------------------

undefinedLocation :: String
undefinedLocation = "GHC.Err.undefined"

-- TODO: will crash if 'undefined' is not used (or explicitly imported) in the source file.
findUndefinedIdT :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Translate c m a Id
findUndefinedIdT = findIdT (TH.mkName undefinedLocation)

-- | Check if the current expression is an undefined value.
isUndefinedValT :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Translate c m CoreExpr ()
isUndefinedValT = prefixFailMsg "not an undefined value: " $
                  withPatFailMsg (wrongExprForm "App (Var undefined) (Type ty)") $
                  do App (Var un) (Type _) <- idR
                     un' <- findUndefinedIdT
                     guardMsg (un == un') ("identifier is not " ++ undefinedLocation)

------------------------------------------------------------------------

errorLocation :: String
errorLocation = "GHC.Err.error"

-- TODO: will crash if 'error' is not used (or explicitly imported) in the source file.
findErrorIdT :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Translate c m a Id
findErrorIdT = findIdT (TH.mkName errorLocation)

-- | Check if the current expression is an undefined value.
isErrorValT :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Translate c m CoreExpr ()
isErrorValT = prefixFailMsg "not an error value: " $
              withPatFailMsg (wrongExprForm "App (App (Var error) (Type ty)) string") $
              do App (App (Var er) (Type _)) _ <- idR
                 er' <- findErrorIdT
                 guardMsg (er == er') ("identifier is not " ++ errorLocation)

------------------------------------------------------------------------

-- | error ty string ==> undefined ty
errorToUndefinedR :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Rewrite c m CoreExpr
errorToUndefinedR = prefixFailMsg "error-to-undefined failed: " (isErrorValT >> replaceWithUndefinedR)

------------------------------------------------------------------------

-- | Make an undefined value of the given type.
mkUndefinedValT :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Type -> Translate c m a CoreExpr
mkUndefinedValT ty =
  do un <- findUndefinedIdT
     return $ App (varToCoreExpr un) (Type ty)

------------------------------------------------------------------------------------------------------

-- | Set the current expression to 'undefined'.
replaceWithUndefinedR :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Rewrite c m CoreExpr
replaceWithUndefinedR = contextfreeT exprTypeM >>= mkUndefinedValT

------------------------------------------------------------------------------------------------------

-- | undefinedExprR = undefinedAppR <+ undefinedLamR <+ undefinedLetR <+ undefinedCastR <+ undefinedTickR <+ undefinedCaseR
undefinedExprR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Rewrite c m CoreExpr
undefinedExprR = setFailMsg "undefined-expr failed."
                   (undefinedAppR <+ undefinedLamR <+ undefinedLetR <+ undefinedCastR <+ undefinedTickR <+ undefinedCaseR)

------------------------------------------------------------------------------------------------------

-- | @(undefined ty1) e@ ==> @undefined ty2@
undefinedAppR :: (BoundVars c, ExtendPath c Crumb, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Rewrite c m CoreExpr
undefinedAppR = prefixFailMsg "undefined-app failed: " $
                do appT isUndefinedValT successT (<>)
                   replaceWithUndefinedR

-- | @(\ v -> undefined ty1)@ ==> @undefined ty2@  (where v is not a 'TyVar')
undefinedLamR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Rewrite c m CoreExpr
undefinedLamR = prefixFailMsg "undefined-lam failed: " $
                do lamT successT isUndefinedValT (<>)
                   replaceWithUndefinedR

-- | let bds in (undefined ty) ==> undefined ty
undefinedLetR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Rewrite c m CoreExpr
undefinedLetR = prefixFailMsg "undefined-let failed: " $
                do letT successT isUndefinedValT (<>)
                   replaceWithUndefinedR

-- | Cast (undefined ty1) co ==> undefined ty2
undefinedCastR :: (BoundVars c, ExtendPath c Crumb, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Rewrite c m CoreExpr
undefinedCastR = prefixFailMsg "undefined-cast failed: " $
                do castT isUndefinedValT successT (<>)
                   replaceWithUndefinedR

-- | Tick tick (undefined ty1) ==> undefined ty1
undefinedTickR :: (BoundVars c, ExtendPath c Crumb, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Rewrite c m CoreExpr
undefinedTickR = prefixFailMsg "undefined-tick failed: " $
                do tickT successT isUndefinedValT (<>)
                   replaceWithUndefinedR

-- | undefinedCaseR = undefinedCaseScrutineeR <+ undefinedCaseAltsR
undefinedCaseR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Rewrite c m CoreExpr
undefinedCaseR = setFailMsg "undefined-case failed" (undefinedCaseScrutineeR <+ undefinedCaseAltsR)

-- | case (undefined ty) of alts ==> undefined ty
undefinedCaseScrutineeR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Rewrite c m CoreExpr
undefinedCaseScrutineeR = prefixFailMsg "undefined-case failed: " $
                 do caseT isUndefinedValT successT successT (const successT) (\ _ _ _ _ -> ())
                    replaceWithUndefinedR

-- | case e of {pat_1 -> undefined ty ; pat_2 -> undefined ty ; ... ; pat_n -> undefined ty} ==> undefined ty
undefinedCaseAltsR :: (AddBindings c, BoundVars c, ExtendPath c Crumb, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => Rewrite c m CoreExpr
undefinedCaseAltsR = prefixFailMsg "undefined-case-alts failed: " $
                     do caseAltT successT successT successT (const (successT,const successT,isUndefinedValT)) (\ _ _ _ _ -> ())
                        replaceWithUndefinedR

------------------------------------------------------------------------

-- | Verify that the given rewrite is a proof that the given expression is a strict function.
verifyStrictT :: (BoundVars c, HasGlobalRdrEnv c, MonadCatch m, HasDynFlags m, MonadThings m) => CoreExpr -> Rewrite c m CoreExpr -> Translate c m a ()
verifyStrictT f r = prefixFailMsg "strictness verification failed: " $
  do (argTy, resTy) <- constT (funArgResTypes f)
     undefArg       <- mkUndefinedValT argTy
     rhs            <- mkUndefinedValT resTy
     let lhs = App f undefArg
     verifyEqualityLeftToRightT lhs rhs r

------------------------------------------------------------------------
