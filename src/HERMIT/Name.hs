{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module HERMIT.Name
    ( HermitName
    , cmpHN2Name
    , cmpHN2Var
    , mkQualified
    , mkUnqualified
    , fromRdrName
    , toRdrName
    , toRdrNames
    , hnModuleName
    , hnUnqualified
    , parseName
    , showName
      -- * Wrappers
    , OccurrenceName(..)
    , OccurrenceNameListBox(..)
    , mkOccPred
    , BindingName(..)
    , mkBindingPred
    , RhsOfName(..)
    , mkRhsOfPred
      -- * Namespaces
    , Named(..)
    , varToNamed
    , allNameSpaces
    , dataConNS
    , tyConClassNS
    , tyVarNS
    , varNS
      -- * Variable Creation
    , newGlobalIdH
    , newIdH
    , newTyVarH
    , newCoVarH
    , newVarH
    , cloneVarH
    , cloneVarFSH
      -- * Name Lookup
    , findId
    , findVar
    , findTyCon
    , findType
    , findInNameSpace
    , findInNameSpaces
    ) where

import Control.Monad
import Control.Monad.IO.Class

import Data.List (intercalate)
import Data.Dynamic (Typeable)
import Data.String (IsString(..))

import HERMIT.Context
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad

-- | Possible results from name lookup.
-- Invariant: One constructor for each NameSpace.
data Named = NamedId Id
           | NamedDataCon DataCon
           | NamedTyCon TyCon
           | NamedTyVar Var
  deriving Typeable

instance Show Named where
    show (NamedId _) = "NamedId"
    show (NamedDataCon _) = "NamedDataCon"
    show (NamedTyCon _) = "NamedTyCon"
    show (NamedTyVar _) = "NamedTyVar"

varToNamed :: Var -> Named
varToNamed v | isVarOcc onm = NamedId v
             | isTvOcc onm  = NamedTyVar v
             | otherwise = error "varToNamed: impossible Var namespace"
    where onm = getOccName v

----------------------- Namespaces -----------------------
-- Simplify what GHC offers a bit, as it has more options
-- that are just duplicates of each other.

tyConClassNS :: NameSpace
tyConClassNS = tcClsName

dataConNS :: NameSpace
dataConNS = dataName

tyVarNS :: NameSpace
tyVarNS = tvName

varNS :: NameSpace
varNS = varNameNS

allNameSpaces :: [NameSpace]
allNameSpaces = [varNS, dataConNS, tyConClassNS, tyVarNS]

----------------------------------------------------------

-- | A 'HermitName' is an optionally fully-qualified name,
-- like GHC's 'RdrName', but without specifying which 'NameSpace'
-- the name is found in.
data HermitName = HermitName { hnModuleName  :: Maybe ModuleName
                             , hnUnqualified :: FastString
                             }
    deriving (Eq, Typeable)

instance Extern HermitName where
    type Box HermitName = HermitName
    box = id
    unbox = id

instance IsString HermitName where fromString = parseName
instance Show HermitName where show = showName

-- | Compare a HermitName to a Var.
--
-- Only compare module names if the HermitName is fully qualified.
-- Otherwise match variables from any module with appropriate occurrence name.
cmpHN2Var :: HermitName -> Var -> Bool
cmpHN2Var hn = cmpHN2Name hn . varName

cmpHN2Name :: HermitName -> Name -> Bool
cmpHN2Name (HermitName hm nm) n
    | Just mn <- hm
    , Just m  <- nameModule_maybe n = (mn == moduleName m) && sameOccName
    | otherwise     = sameOccName
    where sameOccName = nm == occNameFS (getOccName n)

-- | Make a qualified HermitName from a String representing the module name
-- and a String representing the occurrence name.
mkQualified :: String -> String -> HermitName
mkQualified mnm = HermitName (Just $ mkModuleName mnm) . mkFastString

-- | Make an unqualified HermitName from a String.
mkUnqualified :: String -> HermitName
mkUnqualified = HermitName Nothing . mkFastString

-- | Parse a HermitName from a String.
parseName :: String -> HermitName
parseName s | isQualified s = parseQualified s
            | otherwise     = mkUnqualified s

-- | Parse a qualified HermitName from a String.
parseQualified :: String -> HermitName
parseQualified [] = error "parseQualified: empty string"
parseQualified s = mkQualified mnm nm
    where (c:cs) = reverse s -- we are careful to parse 'Prelude..' correctly
          (rNm, _dot:rMod) = break (=='.') cs
          (nm, mnm) = (reverse (c:rNm), reverse rMod)

-- | Turn a HermitName into a (possibly fully-qualified) String.
showName :: HermitName -> String
showName (HermitName mnm nm) = maybe id (\ m n -> moduleNameString m ++ ('.' : n)) mnm $ unpackFS nm

-- | Make a HermitName from a RdrName
fromRdrName :: RdrName -> HermitName
fromRdrName nm = case isQual_maybe nm of
                    Nothing         -> HermitName Nothing    (occNameFS $ rdrNameOcc nm)
                    Just (mnm, onm) -> HermitName (Just mnm) (occNameFS onm)

-- | Make a RdrName for the given NameSpace and HermitName
toRdrName :: NameSpace -> HermitName -> RdrName
toRdrName ns (HermitName mnm nm) = maybe (mkRdrUnqual onm) (flip mkRdrQual onm) mnm
    where onm = mkOccNameFS ns nm

-- | Make a RdrName for each given NameSpace.
toRdrNames :: [NameSpace] -> HermitName -> [RdrName]
toRdrNames nss hnm = [ toRdrName ns hnm | ns <- nss ]

--------------------------------------------------------------------------------------------------

-- Newtype wrappers used for type-based command completion

newtype BindingName = BindingName { unBindingName :: HermitName } deriving Typeable

instance Extern BindingName where
    type Box BindingName = BindingName
    box = id
    unbox = id

mkBindingPred :: BindingName -> Var -> Bool
mkBindingPred (BindingName hnm) = cmpHN2Var hnm

newtype OccurrenceName = OccurrenceName { unOccurrenceName :: HermitName } deriving Typeable

instance Extern OccurrenceName where
    type Box OccurrenceName = OccurrenceName
    box = id
    unbox = id

mkOccPred :: OccurrenceName -> Var -> Bool
mkOccPred (OccurrenceName hnm) = cmpHN2Var hnm

newtype OccurrenceNameListBox = OccurrenceNameListBox [OccurrenceName] deriving Typeable

instance Extern [OccurrenceName] where
    type Box [OccurrenceName] = OccurrenceNameListBox
    box = OccurrenceNameListBox
    unbox (OccurrenceNameListBox l) = l

newtype RhsOfName = RhsOfName { unRhsOfName :: HermitName } deriving Typeable

instance Extern RhsOfName where
    type Box RhsOfName = RhsOfName
    box = id
    unbox = id

mkRhsOfPred :: RhsOfName -> Var -> Bool
mkRhsOfPred (RhsOfName hnm) = cmpHN2Var hnm

--------------------------------------------------------------------------------------------------

-- | An instance of 'MonadThings' for 'Transform', which looks in the context first.
--
-- NB: we store TyVars in the context, but the 'TyThing' return type is not rich enough
-- to return them. So 'lookupThing' cannot be used to look up TyVars.
-- TODO: add function for this, or modify GHC's 'TyThing'?
instance (MonadThings m, BoundVars c) => MonadThings (Transform c m a) where
    lookupThing nm = contextonlyT $ \ c ->
                        case varSetElems $ filterVarSet ((== nm) . varName) (boundVars c) of
                            (i:_) | isVarName nm -> return $ AnId i
                                  | isTyVarName nm -> fail "lookupThing cannot be used with TyVars."
                                  | otherwise -> fail "MonadThings instance for Transform: impossible namespace."
                            []    -> lookupThing nm

--------------------------------------------------------------------------------------------------

findId :: (BoundVars c, LiftCoreM m, HasHermitMEnv m, MonadCatch m, MonadIO m, MonadThings m)
       => HermitName -> c -> m Id
findId nm c = do
    nmd <- findInNameSpaces [varNS, dataConNS] nm c
    case nmd of
        NamedId i -> return i
        NamedDataCon dc -> return $ dataConWrapId dc
        other -> fail $ "findId: impossible Named returned: " ++ show other

findVar :: (BoundVars c, LiftCoreM m, HasHermitMEnv m, MonadCatch m, MonadIO m, MonadThings m)
       => HermitName -> c -> m Var
findVar nm c = do
    nmd <- findInNameSpaces [varNS, tyVarNS, dataConNS] nm c
    case nmd of
        NamedId i -> return i
        NamedTyVar v -> return v
        NamedDataCon dc -> return $ dataConWrapId dc
        other -> fail $ "findVar: impossible Named returned: " ++ show other

findTyCon :: (BoundVars c, LiftCoreM m, HasHermitMEnv m, MonadCatch m, MonadIO m, MonadThings m)
          => HermitName -> c -> m TyCon
findTyCon nm c = do
    nmd <- findInNameSpace tyConClassNS nm c
    case nmd of
        NamedTyCon tc -> return tc
        other -> fail $ "findTyCon: impossible Named returned: " ++ show other

findType :: (BoundVars c, LiftCoreM m, HasHermitMEnv m, MonadCatch m, MonadIO m, MonadThings m)
         => HermitName -> c -> m Type
findType nm c = do
    nmd <- findInNameSpaces [tyVarNS, tyConClassNS] nm c
    case nmd of
        NamedTyVar v -> return $ mkTyVarTy v
        NamedTyCon tc -> return $ mkTyConTy tc
        other -> fail $ "findType: impossible Named returned: " ++ show other

--------------------------------------------------------------------------------------------------

findInNameSpaces :: (BoundVars c, LiftCoreM m, HasHermitMEnv m, MonadCatch m, MonadIO m, MonadThings m)
                 => [NameSpace] -> HermitName -> c -> m Named
findInNameSpaces nss nm c = setFailMsg "Variable not in scope." -- because catchesM clobbers failure messages.
                          $ catchesM [ findInNameSpace ns nm c | ns <- nss ]

findInNameSpace :: (BoundVars c, LiftCoreM m, HasHermitMEnv m, MonadIO m, MonadThings m)
                => NameSpace -> HermitName -> c -> m Named
findInNameSpace ns nm c =
    case varSetElems $ filterVarSet ((== ns) . occNameSpace . getOccName) $ findBoundVars (cmpHN2Var nm) c of
        _ : _ : _ -> fail "multiple matching variables in scope."
        [v]       -> return $ varToNamed v
        []        -> findInNSModGuts ns nm

-- | Looks for Named in current GlobalRdrEnv. If not present, calls 'findInNSPackageDB'.
findInNSModGuts :: (LiftCoreM m, HasHermitMEnv m, MonadIO m, MonadThings m)
                => NameSpace -> HermitName -> m Named
findInNSModGuts ns nm = do
    rdrEnv <- liftM mg_rdr_env getModGuts
    case lookupGRE_RdrName (toRdrName ns nm) rdrEnv of
        [gre] -> nameToNamed $ gre_name gre
        []    -> findInNSPackageDB ns nm
        _     -> fail "findInNSModGuts: multiple names returned"

-- | Looks for Named in package database, or built-in packages.
findInNSPackageDB :: (LiftCoreM m, HasHermitMEnv m, MonadIO m, MonadThings m)
                  => NameSpace -> HermitName -> m Named
findInNSPackageDB ns nm = do
    mnm <- lookupName ns nm
    case mnm of
        Nothing -> findNamedBuiltIn ns nm
        Just n  -> nameToNamed n

-- | Helper to call lookupRdrNameInModule
lookupName :: (HasHermitMEnv m, LiftCoreM m, MonadIO m) => NameSpace -> HermitName -> m (Maybe Name)
lookupName ns nm = case isQual_maybe rdrName of
                    Nothing    -> return Nothing -- we can't use lookupName on the current module
                    Just (m,_) -> do
                        hscEnv <- getHscEnv
                        guts <- getModGuts
                        liftIO $ lookupRdrNameInModule hscEnv guts m rdrName
    where rdrName = toRdrName ns nm

-- | Looks for Named amongst GHC's built-in DataCons/TyCons.
findNamedBuiltIn :: Monad m => NameSpace -> HermitName -> m Named
findNamedBuiltIn ns hnm
    | isValNameSpace ns =
        case [ dc | tc <- wiredInTyCons, dc <- tyConDataCons tc, cmpHN2Name hnm (getName dc) ] of
            [] -> fail "name not in scope."
            [dc] -> return $ NamedDataCon dc
            dcs -> fail $ "multiple DataCons match: " ++ intercalate ", " (map unqualifiedName dcs)
    | isTcClsNameSpace ns =
        case [ tc | tc <- wiredInTyCons, cmpHN2Name hnm (getName tc) ] of
            [] -> fail "type name not in scope."
            [tc] -> return $ NamedTyCon tc
            tcs -> fail $ "multiple TyCons match: " ++ intercalate ", " (map unqualifiedName tcs)
    | otherwise = fail "findNameBuiltIn: unusable NameSpace"

-- | We have a name, find the corresponding Named.
nameToNamed :: MonadThings m => Name -> m Named
nameToNamed n | isVarName n     = liftM NamedId $ lookupId n
              | isDataConName n = liftM NamedDataCon $ lookupDataCon n
              | isTyConName n   = liftM NamedTyCon $ lookupTyCon n
              | isTyVarName n   = fail "nameToNamed: impossible, TyVars are not exported and cannot be looked up."
              | otherwise       = fail "nameToNamed: unknown name type"

-- | Make a 'Name' from a string.
newName :: MonadUnique m => String -> m Name
newName nm = mkSystemVarName <$> getUniqueM <*> return (mkFastString nm)

-- | Make a unique global identifier for a specified type, using a provided name.
newGlobalIdH :: MonadUnique m => String -> Type -> m Id
newGlobalIdH nm ty = mkVanillaGlobal <$> newName nm <*> return ty

-- | Make a unique identifier for a specified type, using a provided name.
newIdH :: MonadUnique m => String -> Type -> m Id
newIdH nm ty = mkLocalId <$> newName nm <*> return ty

-- | Make a unique type variable for a specified kind, using a provided name.
newTyVarH :: MonadUnique m => String -> Kind -> m TyVar
newTyVarH nm k = mkTyVar <$> newName nm <*> return k

-- | Make a unique coercion variable for a specified type, using a provided name.
newCoVarH :: MonadUnique m => String -> Type -> m TyVar
newCoVarH nm ty = mkCoVar <$> newName nm <*> return ty

-- TODO: not sure if the predicates are correct.
-- | Experimental, use at your own risk.
newVarH :: MonadUnique m => String -> KindOrType -> m Var
newVarH name tk | isCoVarType tk = newCoVarH name tk
                | isKind tk      = newTyVarH name tk
                | otherwise      = newIdH name tk

-- | Make a new variable of the same type, with a modified textual name.
cloneVarH :: MonadUnique m => (String -> String) -> Var -> m Var
cloneVarH nameMod v | isTyVar v = newTyVarH name ty
                    | isCoVar v = newCoVarH name ty
                    | isId v    = newIdH name ty
                    | otherwise = fail "If this variable isn't a type, coercion or identifier, then what is it?"
  where
    name = nameMod (unqualifiedName v)
    ty   = varType v

-- | Make a new variable of the same type, with a modified textual name.
cloneVarFSH :: MonadUnique m => (FastString -> FastString) -> Var -> m Var
cloneVarFSH nameMod v | isTyVar v = newTyVarH name ty
                      | isCoVar v = newCoVarH name ty
                      | isId v    = newIdH name ty
                      | otherwise = fail "If this variable isn't a type, coercion or identifier, then what is it?"
  where
    name = unpackFS $ nameMod $ occNameFS $ getOccName v
    ty   = varType v
