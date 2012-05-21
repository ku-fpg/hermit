-- Things that have been copied from GHC, for various reasons.
module Language.HERMIT.GHC where

import GhcPlugins

import Control.Applicative

import Language.KURE
import Language.KURE.Injection

import Language.HERMIT.HermitKure
import Language.HERMIT.External
import Language.HERMIT.HermitEnv

import Language.HERMIT.Primitive.Core
import Data.Maybe (isJust)

import qualified Language.Haskell.TH as TH


ppIdInfo :: Id -> IdInfo -> SDoc
ppIdInfo id info
  = showAttributes
    [ (True, pp_scope <> ppr (idDetails id))
    , (has_arity,      ptext (sLit "Arity=") <> int arity)
    , (has_caf_info,   ptext (sLit "Caf=") <> ppr caf_info)
    , (has_strictness, ptext (sLit "Str=") <> pprStrictness str_info)
    , (has_unf,        ptext (sLit "Unf=") <> ppr unf_info)
    , (not (null rules), ptext (sLit "RULES:") <+> vcat (map ppr rules))
    ]	-- Inline pragma, occ, demand, lbvar info
	-- printed out with all binders (when debug is on);
	-- see PprCore.pprIdBndr
  where
    pp_scope | isGlobalId id   = ptext (sLit "GblId")
    	     | isExportedId id = ptext (sLit "LclIdX")
    	     | otherwise       = ptext (sLit "LclId")

    arity = arityInfo info
    has_arity = arity /= 0

    caf_info = cafInfo info
    has_caf_info = not (mayHaveCafRefs caf_info)

    str_info = strictnessInfo info
    has_strictness = isJust str_info

    unf_info = unfoldingInfo info
    has_unf = hasSomeUnfolding unf_info

    rules = specInfoRules (specInfo info)

showAttributes :: [(Bool,SDoc)] -> SDoc
showAttributes stuff
  | null docs = GhcPlugins.empty
  | otherwise = brackets (sep (punctuate comma docs))
  where
    docs = [d | (True,d) <- stuff]




