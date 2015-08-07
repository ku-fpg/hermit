{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
-- Above shadowing disabled because the eqExprX function has lots of shadowing
module HERMIT.GHC
    ( -- * GHC Imports
      -- | Things that have been copied from GHC, or imported directly, for various reasons.
      module GhcPlugins
    , ppIdInfo
    , zapVarOccInfo
    , thRdrNameGuesses
    , varNameNS
    , isQualified
    , cmpString2Name
    , cmpString2Var
    , qualifiedName
    , unqualifiedName
    , alphaTyVars
    , Type(..)
    , TyLit(..)
    , GhcException(..)
    , throwGhcException
    , throwCmdLineErrorS
    , exprArity
    , occurAnalyseExpr_NoBinderSwap
    , isKind
    , isLiftedTypeKindCon
    , notElemVarSet
    , varSetToStrings
    , showVarSet
    , Pair(..)
    , bndrRuleAndUnfoldingVars
    , coAxiomName
    , CoAxiom.BranchIndex
    , CoAxiom.CoAxiom
    , CoAxiom.Branched
    , Bag.foldBag
    , eqExprX
    , loadSysInterface
    , lookupRdrNameInModule
    , injectDependency
    , reportAllUnsolved
    , zEncodeString
#ifdef mingw32_HOST_OS
    , initStaticOpts
#endif
    , module Class
    , module DsBinds
    , module DsMonad
    , module DynamicLoading
    , module ErrUtils
    , module PrelNames
    , module TcEnv
    , module TcMType
    , module TcRnMonad
    , module TcRnTypes
    , module TcSimplify
    , module TcType
    , module Unify
    , getHscEnvCoreM
    ) where

-- Imports from GHC.
import qualified Bag
import           Class (classTyCon)
import qualified CoAxiom -- for coAxiomName
import           Convert (thRdrNameGuesses)
import           CoreArity
import qualified CoreMonad -- for getHscEnv
import           DsBinds (dsEvBinds)
import           DsMonad (DsM, initDsTc)
import           DynamicLoading (forceLoadTyCon, getValueSafely, lookupRdrNameInModuleForPlugins)
import           Encoding (zEncodeString)
import           ErrUtils (pprErrMsgBag)
import           Finder (findImportedModule, cannotFindModule)
-- we hide these so that they don't get inadvertently used.
-- several are redefined in Core.hs and elsewhere
import           GhcPlugins hiding (exprSomeFreeVars, exprFreeVars, exprFreeIds, bindFreeVars, getHscEnv, RuleName)
import           Kind (isKind,isLiftedTypeKindCon)
import           LoadIface (loadSysInterface)
import qualified OccName -- for varName
import           OccurAnal (occurAnalyseExpr_NoBinderSwap)
import           Pair (Pair(..))
import           Panic (throwGhcException, throwGhcExceptionIO, GhcException(..))
import           PrelNames (typeableClassName)
#ifdef mingw32_HOST_OS
import           StaticFlags
#endif
import           TcEnv (tcLookupClass)
import           TcErrors (reportAllUnsolved)
#if __GLASGOW_HASKELL__ < 710
import           TcMType (newWantedEvVar)
#else
import           TcMType (newEvVar)
#endif
import           TcRnMonad (getCtLoc, initIfaceTcRn)
#if __GLASGOW_HASKELL__ < 710
import           TcRnTypes (TcM, mkNonCanonical, mkFlatWC, CtEvidence(..), SkolemInfo(..), CtOrigin(..))
#else
import           TcRnTypes (TcM, mkNonCanonical, mkSimpleWC, CtEvidence(..), SkolemInfo(..), CtOrigin(..))
#endif
import           TcSimplify (solveWantedsTcM)
import           TcType (mkPhiTy, mkSigmaTy)
import           TypeRep (Type(..),TyLit(..))
import           TysPrim (alphaTyVars)
import           Unify (tcUnifyTys, BindFlag(..))

import Data.List (intercalate)

import HERMIT.GHC.Typechecker

--------------------------------------------------------------------------

-- | Rename this namespace, as 'varName' is already a function in Var.
varNameNS :: NameSpace
varNameNS = OccName.varName

getHscEnvCoreM :: CoreM HscEnv
getHscEnvCoreM = CoreMonad.getHscEnv

--------------------------------------------------------------------------

-- | Convert a 'VarSet' to a list of user-readable strings.
varSetToStrings :: VarSet -> [String]
varSetToStrings = map unqualifiedName . varSetElems

-- | Show a human-readable version of a 'VarSet'.
showVarSet :: VarSet -> String
showVarSet = intercalate ", " . varSetToStrings

--------------------------------------------------------------------------

coAxiomName :: CoAxiom.CoAxiom br -> Name
coAxiomName = CoAxiom.coAxiomName

-- varName :: Var -> Name
-- nameOccName :: Name -> OccName
-- occNameString :: OccName -> String
-- getOccName :: NamedThing a => a -> OccName
-- getName :: NamedThing a => a -> Name
-- getOccString :: NamedThing a => a -> String

-- | Get the unqualified name from a 'NamedThing'.
unqualifiedName :: NamedThing nm => nm -> String
unqualifiedName = getOccString

-- | Get the fully qualified name from a 'Name'.
qualifiedName :: Name -> String
qualifiedName nm = modStr ++ unqualifiedName nm
    where modStr = maybe "" (\m -> moduleNameString (moduleName m) ++ ".") (nameModule_maybe nm)

-- | Compare a 'String' to a 'Name' for equality.
-- Strings containing a period are assumed to be fully qualified names.
-- (Except for ".", which is an unqualified reference to composition.)
cmpString2Name :: String -> Name -> Bool
cmpString2Name str nm | isQualified str = str == qualifiedName nm
                      | otherwise       = str == unqualifiedName nm

isQualified :: String -> Bool
isQualified [] = False
isQualified xs = '.' `elem` init xs -- pathological case is compose (hence the 'init')

-- | Compare a 'String' to a 'Var' for equality. See 'cmpString2Name'.
cmpString2Var :: String -> Var -> Bool
cmpString2Var str = cmpString2Name str . varName

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
    ] -- Inline pragma, occ, demand, lbvar info
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
    has_strictness = True

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

-- This function is copied from GHC, which defines but doesn't expose it.
-- A 'let' can bind a type variable, and idRuleVars assumes
-- it's seeing an Id. This function tests first.
bndrRuleAndUnfoldingVars :: Var -> VarSet
bndrRuleAndUnfoldingVars v | isTyVar v = emptyVarSet
                           | otherwise = idRuleAndUnfoldingVars v

--------------------------------------------------------------------------

-- This function used to be in GHC itself, but was removed.
-- It compares core for equality modulo alpha.
eqExprX :: IdUnfoldingFun -> RnEnv2 -> CoreExpr -> CoreExpr -> Bool
eqExprX id_unfolding_fun env e1 e2
  = go env e1 e2
  where
    go env (Var v1) (Var v2)
      | rnOccL env v1 == rnOccR env v2
      = True

    -- The next two rules expand non-local variables
    -- C.f. Note [Expanding variables] in Rules.lhs
    -- and  Note [Do not expand locally-bound variables] in Rules.lhs
    go env (Var v1) e2
      | not (locallyBoundL env v1)
      , Just e1' <- expandUnfolding_maybe (id_unfolding_fun (lookupRnInScope env v1))
      = go (nukeRnEnvL env) e1' e2

    go env e1 (Var v2)
      | not (locallyBoundR env v2)
      , Just e2' <- expandUnfolding_maybe (id_unfolding_fun (lookupRnInScope env v2))
      = go (nukeRnEnvR env) e1 e2'

    go _   (Lit lit1)    (Lit lit2)      = lit1 == lit2
    go env (Type t1)    (Type t2)        = eqTypeX env t1 t2
    go env (Coercion co1) (Coercion co2) = coreEqCoercion2 env co1 co2
    go env (Cast e1 co1) (Cast e2 co2) = coreEqCoercion2 env co1 co2 && go env e1 e2
    go env (App f1 a1)   (App f2 a2)   = go env f1 f2 && go env a1 a2
    go env (Tick n1 e1)  (Tick n2 e2)  = go_tickish n1 n2 && go env e1 e2

    go env (Lam b1 e1)  (Lam b2 e2)
      =  eqTypeX env (varType b1) (varType b2)   -- False for Id/TyVar combination
      && go (rnBndr2 env b1 b2) e1 e2

    go env (Let (NonRec v1 r1) e1) (Let (NonRec v2 r2) e2)
      =  go env r1 r2  -- No need to check binder types, since RHSs match
      && go (rnBndr2 env v1 v2) e1 e2

    go env (Let (Rec ps1) e1) (Let (Rec ps2) e2)
      = all2 (go env') rs1 rs2 && go env' e1 e2
      where
        (bs1,rs1) = unzip ps1
        (bs2,rs2) = unzip ps2
        env' = rnBndrs2 env bs1 bs2

    go env (Case e1 b1 t1 a1) (Case e2 b2 t2 a2)
      | null a1   -- See Note [Empty case alternatives] in TrieMap
      = null a2 && go env e1 e2 && eqTypeX env t1 t2
      | otherwise
      =  go env e1 e2 && all2 (go_alt (rnBndr2 env b1 b2)) a1 a2

    go _ _ _ = False

    -----------
    go_alt env (c1, bs1, e1) (c2, bs2, e2)
      = c1 == c2 && go (rnBndrs2 env bs1 bs2) e1 e2

    -----------
    go_tickish (Breakpoint lid lids) (Breakpoint rid rids)
      = lid == rid  &&  map (rnOccL env) lids == map (rnOccR env) rids
    go_tickish l r = l == r

locallyBoundL, locallyBoundR :: RnEnv2 -> Var -> Bool
locallyBoundL rn_env v = inRnEnvL rn_env v
locallyBoundR rn_env v = inRnEnvR rn_env v

-- | Finds the 'Name' corresponding to the given 'RdrName' in the context of the 'ModuleName'. Returns @Nothing@ if no
-- such 'Name' could be found. Any other condition results in an exception:
--
-- * If the module could not be found
-- * If we could not determine the imports of the module
--
-- This is adapted from GHC's function called lookupRdrNameInModuleForPlugins,
-- but using initTcFromModGuts instead of initTcInteractive. Also, we ImportBySystem
-- instead of ImportByPlugin, so the EPS gets populated with RULES and instances from
-- the loaded module.
--
-- TODO: consider importing by plugin first, then only importing by system when a name
-- is successfully found... as written we will load RULES/instances if the module loads
-- successfully, even if the name is not found.
lookupRdrNameInModule :: HscEnv -> ModGuts -> ModuleName -> RdrName -> IO (Maybe Name)
lookupRdrNameInModule hsc_env guts mod_name rdr_name = do
    -- First find the package the module resides in by searching exposed packages and home modules
    found_module <- findImportedModule hsc_env mod_name Nothing
    case found_module of
        Found _ mod -> do
            -- Find the exports of the module
            (_, mb_iface) <- initTcFromModGuts hsc_env guts HsSrcFile False $
                             initIfaceTcRn $
                             loadSysInterface doc mod

            case mb_iface of
                Just iface -> do
                    -- Try and find the required name in the exports
                    let decl_spec = ImpDeclSpec { is_mod = mod_name, is_as = mod_name
                                                , is_qual = False, is_dloc = noSrcSpan }
                        provenance = Imported [ImpSpec decl_spec ImpAll]
                        env = mkGlobalRdrEnv (gresFromAvails provenance (mi_exports iface))
                    case lookupGRE_RdrName rdr_name env of
                        [gre] -> return (Just (gre_name gre))
                        []    -> return Nothing
                        _     -> panic "lookupRdrNameInModule"

                Nothing -> throwCmdLineErrorS dflags $ hsep [ptext (sLit "Could not determine the exports of the module"), ppr mod_name]
        err -> throwCmdLineErrorS dflags $ cannotFindModule dflags mod_name err
  where
    dflags = hsc_dflags hsc_env
    doc = ptext (sLit "contains a name used in an invocation of lookupRdrNameInModule")

-- | Also copied from GHC because it is not exposed.
throwCmdLineErrorS :: DynFlags -> SDoc -> IO a
throwCmdLineErrorS dflags = throwCmdLineError . showSDoc dflags

throwCmdLineError :: String -> IO a
throwCmdLineError = throwGhcExceptionIO . CmdLineError

-- | Populate the EPS with a module, as if it were imported in the target program.
injectDependency :: HscEnv -> ModGuts -> ModuleName -> IO ()
injectDependency hsc_env guts mod_name = do
    -- First find the package the module resides in by searching exposed packages and home modules
    found_module <- findImportedModule hsc_env mod_name Nothing
    case found_module of
        Found _ mod -> do
            -- Populate the EPS
            _ <- initTcFromModGuts hsc_env guts HsSrcFile False $
                 initIfaceTcRn $
                 loadSysInterface doc mod
            return ()
        err -> throwCmdLineErrorS dflags $ cannotFindModule dflags mod_name err
  where
    dflags = hsc_dflags hsc_env
    doc = ptext (sLit "dependency injection requested by HERMIT")
