{-# LANGUAGE CPP, InstanceSigs, TypeSynonymInstances, FlexibleInstances #-}
module HERMIT.GHC
    ( -- * GHC Imports
      -- | Things that have been copied from GHC, or imported directly, for various reasons.
      module GhcPlugins
    , ppIdInfo
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
    , occurAnalyseExpr
    , isKind
    , isLiftedTypeKindCon
    , exprType -- TODO: remove once we can use GHC's exprType again
#if __GLASGOW_HASKELL__ > 706
    , coAxiomName
    , CoAxiom.BranchIndex
    , CoAxiom.CoAxiom
    , CoAxiom.Branched
#endif
    , notElemVarSet
    , varSetToStrings
    , showVarSet
    , Pair(..)
    , bndrRuleAndUnfoldingVars
#if __GLASGOW_HASKELL__ <= 706
    , Control.Monad.IO.Class.liftIO
#endif
    , runDsMtoCoreM
    , runTcMtoCoreM
    , buildDictionary
    ) where

#if __GLASGOW_HASKELL__ <= 706
-- GHC 7.6
import qualified Control.Monad.IO.Class
import qualified MonadUtils (MonadIO,liftIO)
import GhcPlugins hiding (exprFreeVars, exprFreeIds, bindFreeVars, exprType, liftIO)
#else
#if __GLASGOW_HASKELL__ < 708
-- TODO: remove this case once 7.8 comes out, only here because
-- my HEAD installs are pre-8522 patch, and I don't want to rebuild
-- on four different machines just yet.
-- GHC 7.7.XXX
import GhcPlugins hiding (exprFreeVars, exprFreeIds, bindFreeVars, exprType) -- we hide these so that they don't get inadvertently used.  See Core.hs
#else
-- GHC 7.8
import GhcPlugins hiding (exprFreeVars, exprFreeIds, bindFreeVars) -- we hide these so that they don't get inadvertently used.  See Core.hs
#endif
#endif

-- hacky direct GHC imports
import qualified Bag
import Class (classTyCon)
import Convert (thRdrNameGuesses)
import CoreArity
import DsBinds (dsEvBinds)
import DsMonad (DsM)
import Kind (isKind,isLiftedTypeKindCon)
import OccurAnal (occurAnalyseExpr)
import Pair (Pair(..))
import Panic (GhcException(ProgramError), throwGhcException)
import PprCore (pprCoreExpr)
import PrelNames (typeableClassName)
import TcEnv (tcLookupClass)
import TcMType (newWantedEvVar)
import TcRnMonad (getCtLoc)
import TcRnTypes (TcM, mkNonCanonical, mkFlatWC, CtEvidence(..), SkolemInfo(..), CtOrigin(..))
import TcSimplify (solveWantedsTcM)
import TypeRep (Type(..),TyLit(..))
import TysPrim (alphaTy, alphaTyVars)

#if __GLASGOW_HASKELL__ <= 706
import Data.Maybe (isJust)
#else
import qualified CoAxiom -- for coAxiomName
#endif

import Data.List (intercalate)
import Data.Monoid hiding ((<>))

import HERMIT.GHC.Typechecker

import qualified Language.Haskell.TH as TH

--------------------------------------------------------------------------

#if __GLASGOW_HASKELL < 708
-- Note: once 7.8 comes out, change condition above to "<= 706"
exprType :: CoreExpr -> Type
-- ^ Recover the type of a well-typed Core expression. Fails when
-- applied to the actual 'CoreSyn.Type' expression as it cannot
-- really be said to have a type
exprType (Var var)           = idType var
exprType (Lit lit)           = literalType lit
exprType (Coercion co)       = coercionType co
exprType (Let bind body)
  | NonRec tv rhs <- bind
  , Type ty <- rhs           = substTyWith [tv] [ty] (exprType body)
  | otherwise                = exprType body
exprType (Case _ _ ty _)     = ty
exprType (Cast _ co)         = pSnd (coercionKind co)
exprType (Tick _ e)          = exprType e
exprType (Lam binder expr)   = mkPiType binder (exprType expr)
exprType e@(App _ _)
  = case collectArgs e of
        (fun, args) -> applyTypeToArgs e (exprType fun) args

exprType other = pprTrace "exprType" (pprCoreExpr other) alphaTy
#endif

--------------------------------------------------------------------------

-- | Convert a 'VarSet' to a list of user-readable strings.
varSetToStrings :: VarSet -> [String]
varSetToStrings = map var2String . varSetElems

-- | Show a human-readable version of a 'VarSet'.
showVarSet :: VarSet -> String
showVarSet = intercalate ", " . varSetToStrings

--------------------------------------------------------------------------

#if __GLASGOW_HASKELL__ <= 706
-- coAxiomName :: CoAxiom -> Name
-- coAxiomName = coAxiomName
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
    , (notNull rules,  ptext (sLit "RULES:") <+> vcat (map ppr rules))
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

instance Monoid VarSet where
  mempty :: VarSet
  mempty = emptyVarSet

  mappend :: VarSet -> VarSet -> VarSet
  mappend = unionVarSet

--------------------------------------------------------------------------

#if __GLASGOW_HASKELL__ <= 706
instance Control.Monad.IO.Class.MonadIO CoreM where
  liftIO :: IO a -> CoreM a
  liftIO = MonadUtils.liftIO
#endif

--------------------------------------------------------------------------

-- This function is copied from GHC, which defines but doesn't expose it.
-- A 'let' can bind a type variable, and idRuleVars assumes
-- it's seeing an Id. This function tests first.
bndrRuleAndUnfoldingVars :: Var -> VarSet
bndrRuleAndUnfoldingVars v | isTyVar v = emptyVarSet
                           | otherwise = idRuleAndUnfoldingVars v
  
--------------------------------------------------------------------------

-- TODO: this interface can change however needed
runTcMtoCoreM :: ModGuts -> TcM a -> CoreM a
runTcMtoCoreM guts m = do
    env <- getHscEnv
    -- What is the effect of HsSrcFile (should we be using something else?)
    -- What should the boolean flag be set to?
    (msgs, mr) <- liftIO $ initTcFromModGuts env guts HsSrcFile False (mg_module guts) m
    -- There is probably something better for reporting the errors.
    let dumpSDocs endMsg = Bag.foldBag (\ d r -> d ++ ('\n':r)) show endMsg
        showMsgs (warns, errs) = "Errors:\n" ++ dumpSDocs ("Warnings:\n" ++ dumpSDocs "" warns) errs
    maybe (fail $ showMsgs msgs) return mr

runDsMtoCoreM :: DsM a -> CoreM a
runDsMtoCoreM _m = fail "runDsMtoCoreM unimplemented"

buildDictionary :: ModGuts -> Type -> CoreM [CoreBind]
buildDictionary guts ty = do
    dflags <- getDynFlags
    bnds <- runTcMtoCoreM guts $ do
        cls <- tcLookupClass typeableClassName
        liftIO $ putStrLn $ "class: " ++ (showPpr dflags cls)
        liftIO $ putStrLn $ "classTyCon: " ++ (showPpr dflags $ classTyCon cls)
        liftIO $ putStrLn $ "tyConKind: " ++ (showPpr dflags $ tyConKind $ classTyCon cls)
        let predTy = mkClassPred cls [typeKind ty, ty] -- recall that Typeable is now poly-kinded
        liftIO $ putStrLn $ "isPredTy: " ++ (show $ isPredTy predTy)
        liftIO $ putStrLn $ "predTy: " ++ (showPpr dflags $ predTy)
        liftIO $ putStrLn $ "typeKind: " ++ (showPpr dflags $ typeKind predTy)
        loc <- getCtLoc $ GivenOrigin UnkSkol
        evar <- newWantedEvVar predTy
        let nonC = mkNonCanonical loc $ CtWanted { ctev_pred = predTy, ctev_evar = evar }
            wCs = mkFlatWC [nonC]
        (_wCs', bnds) <- solveWantedsTcM wCs
        return bnds
    liftIO $ putStrLn $ showPpr dflags bnds
    runDsMtoCoreM $ dsEvBinds bnds

