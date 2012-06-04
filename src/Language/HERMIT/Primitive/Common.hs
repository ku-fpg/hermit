-- | Note: this module should NOT export externals. It is for common
--   transformations needed by the other primitive modules.
module Language.HERMIT.Primitive.Common where

import GhcPlugins

import Control.Applicative
import Control.Arrow

import Data.List

import Language.HERMIT.HermitKure

import Language.HERMIT.Primitive.GHC

-- | List of variables bound in binding (including type variables)
bindings :: TranslateH CoreBind [Var]
bindings = recT (\_ -> arr (\(Def v _) -> v)) id
        <+ nonRecT idR (\v _ -> [v])

-- | List of variables bound by Let (including type variables)
letVarsT :: TranslateH CoreExpr [Var]
letVarsT = letT bindings idR const

-- | List of Ids bound by the case alternative
altVarsT :: TranslateH CoreAlt [Id]
altVarsT = altT (pure ()) (const const)

-- | List of the list of Ids bound by each case alternative
caseAltVarsT :: TranslateH CoreExpr [[Id]]
caseAltVarsT = caseT (pure ()) (const altVarsT) $ \ _ i _ ids -> map (i:) ids

-- | Free variables for a CoreAlt, returns a function, which accepts
--   the coreBndr name, before giving a result.
--   This is so we can use this with congruence combinators:
--
--   caseT id (const altFreeVarsT) $ \ _ bndr _ fs -> [ f bndr | f <- fs ]
altFreeVarsT :: TranslateH CoreAlt (Id -> [Var])
altFreeVarsT = altT freeVarsT $ \ _con ids frees coreBndr -> nub frees \\ nub (coreBndr : ids)
