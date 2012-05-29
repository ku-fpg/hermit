-- Things that have been copied from GHC, or imported directly, for various reasons.
module Language.HERMIT.GHC
        ( ppIdInfo
        , thRdrNameGuesses
        , cmpTHName2Name
        , findNameFromTH
        , alphaTyVars
        ) where

import GhcPlugins

-- hacky direct GHC imports
import Convert (thRdrNameGuesses)
import TysPrim          ( alphaTyVars )

import Data.Maybe (isJust)
import qualified Language.Haskell.TH as TH

--------------------------------------------------------------------------

-- Hacks till we can find the correct way of doing these.
cmpTHName2Name :: TH.Name -> Name -> Bool
cmpTHName2Name th_nm ghc_nm = TH.nameBase th_nm == occNameString (nameOccName ghc_nm)

-- This is hopeless O(n), because the we could not generate the OccName's that match,
-- for use of the GHC OccEnv.
findNameFromTH :: GlobalRdrEnv -> TH.Name -> [Name]
findNameFromTH rdrEnv nm =
        [ gre_name elt
        | elt <- concat $ occEnvElts rdrEnv
        , cmpTHName2Name nm (gre_name elt)
        ]

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
  | null docs = empty
  | otherwise = brackets (sep (punctuate comma docs))
  where
    docs = [d | (True,d) <- stuff]

--------------------------------------------------------------------------




