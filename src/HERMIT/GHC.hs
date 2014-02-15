{-# LANGUAGE CPP, InstanceSigs, TypeSynonymInstances, FlexibleInstances #-}
module HERMIT.GHC
    ( -- * GHC Imports
      -- | Things that have been copied from GHC, or imported directly, for various reasons.
      module GhcPlugins
    , ppIdInfo
    , zapVarOccInfo
    , var2String
    , thRdrNameGuesses
    , cmpString2Name
    , cmpString2Var
    , fqName
    , uqName
    , findNamesFromString
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
#else
    , runDsMtoCoreM
    , runTcMtoCoreM
    , buildTypeable
    , eqExprX
#endif
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
import Convert (thRdrNameGuesses)
import CoreArity
import Kind (isKind,isLiftedTypeKindCon)
import OccurAnal (occurAnalyseExpr)
import Pair (Pair(..))
import Panic (GhcException(ProgramError), throwGhcException)
import PprCore (pprCoreExpr)
import TypeRep (Type(..),TyLit(..))
import TysPrim (alphaTy, alphaTyVars)

#if __GLASGOW_HASKELL__ <= 706
import Data.Maybe (isJust)
#else
import qualified Bag
import qualified CoAxiom -- for coAxiomName
import DsBinds (dsEvBinds)
import DsMonad (DsM, initDsTc)
import PrelNames (typeableClassName)
import TcEnv (tcLookupClass)
import TcMType (newWantedEvVar)
import TcRnMonad (getCtLoc)
import TcRnTypes (TcM, mkNonCanonical, mkFlatWC, CtEvidence(..), SkolemInfo(..), CtOrigin(..))
import TcSimplify (solveWantedsTcM)

import HERMIT.GHC.Typechecker
#endif

import Data.List (intercalate)
import Data.Monoid hiding ((<>))

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

-- | Compare a 'String' to a 'Name' for equality.
-- Strings containing a period are assumed to be fully qualified names.
-- (Except for ".", which is an unqualified reference to composition.)
cmpString2Name :: String -> Name -> Bool
cmpString2Name str nm | isQualified str = str == fqName nm
                      | otherwise       = str == uqName nm

isQualified :: String -> Bool
isQualified [] = False
isQualified xs = '.' `elem` init xs -- pathological case is compose (hence the 'init')

-- | Compare a 'String' to a 'Var' for equality. See 'cmpString2Name'.
cmpString2Var :: String -> Var -> Bool
cmpString2Var str = cmpString2Name str . varName

-- | Find 'Name's matching a given fully qualified or unqualified name.
findNamesFromString :: GlobalRdrEnv -> String -> [Name]
findNamesFromString rdrEnv str | isQualified str = res
                               | otherwise       = res
    where res = [ nm | elt <- globalRdrEnvElts rdrEnv, let nm = gre_name elt, cmpString2Name str nm ]

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

#if __GLASGOW_HASKELL__ > 706
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

runDsMtoCoreM :: ModGuts -> DsM a -> CoreM a
runDsMtoCoreM guts = runTcMtoCoreM guts . initDsTc

-- TODO: 
buildTypeable :: ModGuts -> Type -> CoreM (Id, [CoreBind])
buildTypeable guts ty = do
    (i, bs) <- runTcMtoCoreM guts $ do
        cls <- tcLookupClass typeableClassName
        let predTy = mkClassPred cls [typeKind ty, ty] -- recall that Typeable is now poly-kinded
        loc <- getCtLoc $ GivenOrigin UnkSkol
        evar <- newWantedEvVar predTy
        let nonC = mkNonCanonical $ CtWanted { ctev_pred = predTy, ctev_evar = evar, ctev_loc = loc }
            wCs = mkFlatWC [nonC]
        (_wCs', bnds) <- solveWantedsTcM wCs
        -- TODO: check for unsolved constraints?
        return (evar, bnds)
    bnds <- runDsMtoCoreM guts $ dsEvBinds bs
    return (i,bnds)

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
#endif
