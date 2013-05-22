{-# LANGUAGE CPP #-}
module Language.HERMIT.GHC
    ( -- * GHC Imports
      -- | Things that have been copied from GHC, or imported directly, for various reasons.
      ppIdInfo
    , var2String
    , thRdrNameGuesses
    , name2THName
    , var2THName
    , cmpTHName2Name
    , cmpString2Name
    , cmpTHName2Var
    , cmpString2Var
    , unqualifiedVarName
    , findNameFromTH
    , alphaTyVars
    , Type(..)
    , TyLit(..)
    , GhcException(..)
    , throwGhcException
    , exprArity
    , coAxiomName
    ) where

import GhcPlugins as GHC

-- hacky direct GHC imports
import Convert (thRdrNameGuesses)
import TysPrim (alphaTyVars)
import TypeRep (Type(..),TyLit(..))
import Panic (GhcException(ProgramError), throwGhcException)
import CoreArity

#if __GLASGOW_HASKELL__ <= 706
import Data.Maybe (isJust)
#else
import qualified CoAxiom -- for coAxiomName
#endif
import qualified Language.Haskell.TH as TH

--------------------------------------------------------------------------

#if __GLASGOW_HASKELL__ <= 706
coAxiomName :: CoAxiom -> Name
coAxiomName = GHC.coAxiomName
#else
coAxiomName :: CoAxiom.CoAxiom br -> Name
coAxiomName = CoAxiom.coAxiomName
#endif

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
var2String = occNameString . nameOccName . varName -- TODO: would getOccString be okay here?

-- | Converts a GHC 'Name' to a Template Haskell 'TH.Name', going via a 'String'.
name2THName :: Name -> TH.Name
name2THName = TH.mkName . getOccString

-- | Converts an 'Var' to a Template Haskell 'TH.Name', going via a 'String'.
var2THName :: Var -> TH.Name
var2THName = name2THName . varName

-- | Get the unqualified name from an 'Var'.
unqualifiedVarName :: Var -> String
unqualifiedVarName = TH.nameBase . var2THName

-- | Hacks until we can find the correct way of doing these.
cmpTHName2Name :: TH.Name -> Name -> Bool
cmpTHName2Name th_nm = cmpString2Name (TH.nameBase th_nm)

-- | Hacks until we can find the correct way of doing these.
cmpString2Name :: String -> Name -> Bool
cmpString2Name str nm = str == getOccString nm -- occNameString (nameOccName ghc_nm)

-- | Hacks until we can find the correct way of doing these.
cmpTHName2Var :: TH.Name -> Var -> Bool
cmpTHName2Var nm = cmpTHName2Name nm . varName

-- | Hacks until we can find the correct way of doing these.
cmpString2Var :: String -> Var -> Bool
cmpString2Var str = cmpString2Name str . varName

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
    has_strictness =
#if __GLASGOW_HASKELL__ > 706
        True
#else
        isJust str_info
#endif

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




