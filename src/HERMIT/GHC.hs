{-# LANGUAGE CPP #-}
module HERMIT.GHC
    ( -- * GHC Imports
      -- | Things that have been copied from GHC, or imported directly, for various reasons.
      ppIdInfo
    , zapVarOccInfo
    , var2String
    , thRdrNameGuesses
    , name2THName
    , var2THName
    , cmpTHName2Name
    , cmpString2Name
    , cmpTHName2Var
    , cmpString2Var
    , fqName
    , uqName
    , findNamesFromString
    , findNamesFromTH
    , alphaTyVars
    , Type(..)
    , TyLit(..)
    , GhcException(..)
    , throwGhcException
    , exprArity
    , isKind
    , isLiftedTypeKindCon
    , HERMIT.GHC.coAxiomName
#if __GLASGOW_HASKELL__ > 706
    , CoAxiom.BranchIndex
    , CoAxiom.CoAxiom
    , CoAxiom.Branched
#endif
    , notElemVarSet
    ) where

import GhcPlugins as GHC

-- hacky direct GHC imports
import Convert (thRdrNameGuesses)
import TysPrim (alphaTyVars)
import TypeRep (Type(..),TyLit(..))
import Panic (GhcException(ProgramError), throwGhcException)
import CoreArity
import Kind (isKind,isLiftedTypeKindCon)

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
-- showName :: TH.Name -> String
-- TH.mkName :: String -> TH.Name

-- | Get the unqualified name from a 'NamedThing'.
uqName :: NamedThing nm => nm -> String
uqName = getOccString

-- | Get the fully qualified name from a 'Name'.
fqName :: Name -> String
fqName nm = modStr ++ uqName nm
    where modStr = maybe "" (\m -> moduleNameString (moduleName m) ++ ".") (nameModule_maybe nm)

-- | Convert a variable to a neat string for printing (unqualfied name).
var2String :: Var -> String
var2String = uqName . varName

-- | Converts a GHC 'Name' to a Template Haskell 'TH.Name', going via a 'String'.
name2THName :: Name -> TH.Name
name2THName = TH.mkName . uqName

-- | Converts an 'Var' to a Template Haskell 'TH.Name', going via a 'String'.
var2THName :: Var -> TH.Name
var2THName = name2THName . varName

-- | Compare a 'String' to a 'Name' for equality.
-- Strings containing a period are assumed to be fully qualified names.
cmpString2Name :: String -> Name -> Bool
cmpString2Name str nm | isQualified str = str == fqName nm
                      | otherwise       = str == uqName nm

isQualified :: String -> Bool
isQualified [] = False
isQualified xs = '.' `elem` init xs -- pathological case is compose

-- | Compare a 'String' to a 'Var' for equality. See 'cmpString2Name'.
cmpString2Var :: String -> Var -> Bool
cmpString2Var str = cmpString2Name str . varName

-- | Compare a 'TH.Name' to a 'Name' for equality. See 'cmpString2Name'.
cmpTHName2Name :: TH.Name -> Name -> Bool
cmpTHName2Name th_nm = cmpString2Name (show th_nm)

-- | Compare a 'TH.Name' to a 'Var' for equality. See 'cmpString2Name'.
cmpTHName2Var :: TH.Name -> Var -> Bool
cmpTHName2Var nm = cmpTHName2Name nm . varName

-- | Find 'Name's matching a given fully qualified or unqualified name.
-- If given name is fully qualified, will only return first result, which is assumed unique.
findNamesFromString :: GlobalRdrEnv -> String -> [Name]
findNamesFromString rdrEnv str | isQualified str = take 1 res
                               | otherwise       = res
    where res = [ nm | elt <- globalRdrEnvElts rdrEnv, let nm = gre_name elt, cmpString2Name str nm ]

-- | Find 'Name's matching a 'TH.Name'. See 'findNamesFromString'.
findNamesFromTH :: GlobalRdrEnv -> TH.Name -> [Name]
findNamesFromTH rdrEnv = findNamesFromString rdrEnv . show

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

-- | Erase all 'OccInfo' in a variable if it is is an 'Id', or do nothing if it's a 'TyVar' or 'CoVar' (which have no 'OccInfo').
zapVarOccInfo :: Var -> Var
zapVarOccInfo i = if isId i
                    then zapIdOccInfo i
                    else i

--------------------------------------------------------------------------

-- | Determine if a 'Var' is not an element of a 'VarSet'.
notElemVarSet :: Var -> VarSet -> Bool
notElemVarSet v vs = not (v `elemVarSet` vs)

--------------------------------------------------------------------------
