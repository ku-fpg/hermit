module Language.HERMIT.GHC
        (
        -- | Things that have been copied from GHC, or imported directly, for various reasons.
          ppIdInfo
        , var2String
        , thRdrNameGuesses
        , name2THName
        , id2THName
        , cmpTHName2Name
        , cmpString2Name
        , cmpTHName2Id
        , cmpString2Id
        , unqualifiedIdName
        , findNameFromTH
        , alphaTyVars
        , Type(..)
        , GhcException(..)
        , throwGhcException
        , exprArity
) where

import GhcPlugins

-- hacky direct GHC imports
import Convert (thRdrNameGuesses)
import TysPrim (alphaTyVars)
import TypeRep (Type(..))
import Panic (GhcException(ProgramError), throwGhcException)
import CoreArity

import Data.Maybe (isJust)
import qualified Language.Haskell.TH as TH

--------------------------------------------------------------------------

-- idName :: Id -> Name
-- varName :: Var -> Name
-- nameOccName :: Name -> OccName
-- occNameString :: OccName -> String
-- getOccName :: NamedThing a => a -> OccName
-- getName :: NamedThing a => a -> Name
-- getOccString :: NamedThing a => a -> String

-- TH.nameBase :: TH.Name -> String
-- TH.mkName :: String -> TH.Name

-- | Convert a variable to a neat string for printing.
var2String :: Var -> String
var2String = occNameString . nameOccName . varName

-- | Converts a GHC 'Name' to a Template Haskell 'TH.Name', going via a 'String'.
name2THName :: Name -> TH.Name
name2THName = TH.mkName . getOccString

-- | Converts an 'Id' to a Template Haskell 'TH.Name', going via a 'String'.
id2THName :: Id -> TH.Name
id2THName = name2THName . idName

-- | Get the unqualified name from an Id/Var.
unqualifiedIdName :: Id -> String
unqualifiedIdName = TH.nameBase . id2THName

-- | Hacks until we can find the correct way of doing these.
cmpTHName2Name :: TH.Name -> Name -> Bool
cmpTHName2Name th_nm = cmpString2Name (TH.nameBase th_nm)

-- | Hacks until we can find the correct way of doing these.
cmpString2Name :: String -> Name -> Bool
cmpString2Name str_nm ghc_nm = str_nm == getOccString ghc_nm -- occNameString (nameOccName ghc_nm)

-- | Hacks until we can find the correct way of doing these.
cmpTHName2Id :: TH.Name -> Id -> Bool
cmpTHName2Id nm = cmpTHName2Name nm . idName

-- | Hacks until we can find the correct way of doing these.
cmpString2Id :: String -> Id -> Bool
cmpString2Id str_nm = cmpString2Name str_nm . idName

-- | This is hopeless O(n), because the we could not generate the 'OccName's that match,
-- for use of the GHC 'OccEnv'.
findNameFromTH :: GlobalRdrEnv -> TH.Name -> [Name]
findNameFromTH rdrEnv nm =
        [ gre_name elt
        | elt <- concat $ occEnvElts rdrEnv
        , cmpTHName2Name nm (gre_name elt)
        ]

-- | Pretty-print an identifier.
ppIdInfo :: Id -> IdInfo -> SDoc
ppIdInfo v info
  = showAttributes
    [ (True, pp_scope <> ppr (idDetails v))
    , (has_arity,      ptext (sLit "Arity=") <> int arity)
    , (has_caf_info,   ptext (sLit "Caf=") <> ppr caf_info)
    , (has_strictness, ptext (sLit "Str=") <> pprStrictness str_info)
    , (has_unf,        ptext (sLit "Unf=") <> ppr unf_info)
    , (not (null rules), ptext (sLit "RULES:") <+> vcat (map ppr rules))
    ]	-- Inline pragma, occ, demand, lbvar info
	-- printed out with all binders (when debug is on);
	-- see PprCore.pprIdBndr
  where
    pp_scope | isGlobalId v   = ptext (sLit "GblId")
    	     | isExportedId v = ptext (sLit "LclIdX")
    	     | otherwise      = ptext (sLit "LclId")

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




