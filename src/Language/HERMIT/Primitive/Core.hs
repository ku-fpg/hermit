{-# LANGUAGE TypeFamilies, FlexibleInstances #-}

-- These are reflections of some GHC utilties, but inside HERMIT.

-- Placeholder for new prims
module Language.HERMIT.Primitive.Core where

import GhcPlugins hiding ((<>))
import qualified Data.Map as Map

import Language.KURE

import Language.HERMIT.Types
import Language.HERMIT.External
import Language.HERMIT.HermitEnv as Env
import Language.HERMIT.HermitMonad as M

import qualified Language.Haskell.TH as TH

newVarH :: TH.Name -> Type -> HermitM Id
newVarH nm ty = do
        liftIO $ putStrLn "\n((newVarH))"
        liftIO $ print nm
        let fast_str = mkFastString (show nm)
        liftIO $ print fast_str
        uq <- getUniqueM

        let name = mkSystemVarName uq fast_str

        liftIO $ putStr (showSDoc (ppr name))

        let loc_id = mkLocalId name ty

        liftIO $ putStr (showSDoc (ppr loc_id))

        liftIO $ print "Done new VarH "

        return $ loc_id

newTypeVarH :: TH.Name -> Kind -> HermitM TyVar
newTypeVarH = undefined

{-
-- freeVarH :: CoreExpr -> Var
freeVarsH

-}


-- NOTE:  this is not a Translate.
-- We directly invoke a CoreUtils function to return all Free Var's
-- appearing anywhere in/below the CoreExpr.
freeIds :: CoreExpr -> [Id]
freeIds  = uniqSetToList . exprFreeIds
