{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleInstances, TypeFamilies #-}
#if __GLASGOW_HASKELL__ <= 706
{-# LANGUAGE ScopedTypeVariables #-}
#endif
module HERMIT.Name
    ( HermitName
    , OccurrenceName(..)
    , OccurrenceNameListBox(..)
    , mkOccPred
    , BindingName(..)
    , mkBindingPred
    , RhsOfName(..)
    , mkRhsOfPred
    , fromRdrName
    , toRdrName
    , toRdrNames
    , hnModuleName
    , hnUnqualified
    , parseName
    , showName
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
      -- * Name Lookup
    , findId
#if __GLASGOW_HASKELL__ > 706
    , findVar
    , findTyCon
    , findType
    , findInNameSpace
    , findInNameSpaces
#endif
    ) where

import Control.Monad
import Control.Monad.IO.Class

#if __GLASGOW_HASKELL__ <= 706
import Data.List (intercalate)
#endif
import Data.Dynamic (Typeable)

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
                             , hnUnqualified :: String
                             }
    deriving Typeable

instance Extern HermitName where
    type Box HermitName = HermitName
    box = id
    unbox = id

-- | Parse a HermitName from a String.
parseName :: String -> HermitName
parseName s | isQualified s = parseQualified s
            | otherwise     = mkUnqualified s

-- | Turn a HermitName into a (possibly fully-qualified) String.
showName :: HermitName -> String
showName (HermitName mnm nm) = maybe id (\ m n -> moduleNameString m ++ ('.' : n))  mnm nm

mkQualified :: String -> String -> HermitName
mkQualified mnm nm = HermitName (Just $ mkModuleName mnm) nm

mkUnqualified :: String -> HermitName
mkUnqualified = HermitName Nothing

fromRdrName :: RdrName -> HermitName
fromRdrName nm = case isQual_maybe nm of
                    Nothing         -> HermitName Nothing    (occNameString $ rdrNameOcc nm)
                    Just (mnm, onm) -> HermitName (Just mnm) (occNameString onm)

-- | Make a RdrName for the given NameSpace and HermitName
toRdrName :: NameSpace -> HermitName -> RdrName
toRdrName ns (HermitName mnm nm) = maybe (mkRdrUnqual onm) (flip mkRdrQual onm) mnm
    where onm = mkOccName ns nm

-- | Make a RdrName for each given NameSpace.
toRdrNames :: [NameSpace] -> HermitName -> [RdrName]
toRdrNames nss hnm = [ toRdrName ns hnm | ns <- nss ]

parseQualified :: String -> HermitName
parseQualified [] = error "parseQualified: empty string"
parseQualified s = mkQualified mnm nm
    where (c:cs) = reverse s -- we are careful to parse 'Prelude..' correctly
          (rNm, _dot:rMod) = break (=='.') cs
          (nm, mnm) = (reverse (c:rNm), reverse rMod)

--------------------------------------------------------------------------------------------------

-- Newtype wrappers used for type-based command completion
-- TODO: change String to HermitName

newtype BindingName = BindingName { unBindingName :: String } deriving Typeable

instance Extern BindingName where
    type Box BindingName = BindingName
    box = id
    unbox = id

mkBindingPred :: BindingName -> Var -> Bool
mkBindingPred (BindingName str) = cmpString2Var str

newtype OccurrenceName = OccurrenceName { unOccurrenceName :: String } deriving Typeable

instance Extern OccurrenceName where
    type Box OccurrenceName = OccurrenceName
    box = id
    unbox = id

mkOccPred :: OccurrenceName -> Var -> Bool
mkOccPred (OccurrenceName str) = cmpString2Var str

newtype OccurrenceNameListBox = OccurrenceNameListBox [OccurrenceName] deriving Typeable

instance Extern [OccurrenceName] where
    type Box [OccurrenceName] = OccurrenceNameListBox
    box = OccurrenceNameListBox
    unbox (OccurrenceNameListBox l) = l

newtype RhsOfName = RhsOfName { unRhsOfName :: String } deriving Typeable

instance Extern RhsOfName where
    type Box RhsOfName = RhsOfName
    box = id
    unbox = id

mkRhsOfPred :: RhsOfName -> Var -> Bool
mkRhsOfPred (RhsOfName str) = cmpString2Var str

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

#if __GLASGOW_HASKELL__ > 706
findId :: (BoundVars c, HasHscEnv m, HasHermitMEnv m, MonadCatch m, MonadIO m, MonadThings m)
       => String -> c -> m Id
findId nm c = do
    nmd <- findInNameSpaces [varNS, dataConNS] nm c
    case nmd of
        NamedId i -> return i
        NamedDataCon dc -> return $ dataConWrapId dc
        other -> fail $ "findId: impossible Named returned: " ++ show other

findVar :: (BoundVars c, HasHscEnv m, HasHermitMEnv m, MonadCatch m, MonadIO m, MonadThings m)
       => String -> c -> m Var
findVar nm c = do
    nmd <- findInNameSpaces [varNS, tyVarNS, dataConNS] nm c
    case nmd of
        NamedId i -> return i
        NamedTyVar v -> return v
        NamedDataCon dc -> return $ dataConWrapId dc
        other -> fail $ "findVar: impossible Named returned: " ++ show other

findTyCon :: (BoundVars c, HasHscEnv m, HasHermitMEnv m, MonadCatch m, MonadIO m, MonadThings m)
          => String -> c -> m TyCon
findTyCon nm c = do
    nmd <- findInNameSpace tyConClassNS nm c
    case nmd of
        NamedTyCon tc -> return tc
        other -> fail $ "findTyCon: impossible Named returned: " ++ show other

findType :: (BoundVars c, HasHscEnv m, HasHermitMEnv m, MonadCatch m, MonadIO m, MonadThings m)
         => String -> c -> m Type
findType nm c = do
    nmd <- findInNameSpaces [tyVarNS, tyConClassNS] nm c
    case nmd of
        NamedTyVar v -> return $ mkTyVarTy v
        NamedTyCon tc -> return $ mkTyConTy tc
        other -> fail $ "findType: impossible Named returned: " ++ show other

--------------------------------------------------------------------------------------------------

findInNameSpaces :: (BoundVars c, HasHscEnv m, HasHermitMEnv m, MonadCatch m, MonadIO m, MonadThings m)
                 => [NameSpace] -> String -> c -> m Named
findInNameSpaces nss nm c = setFailMsg "Variable not in scope." -- because catchesM clobbers failure messages.
                          $ catchesM [ findInNameSpace ns nm c | ns <- nss ]

findInNameSpace :: (BoundVars c, HasHscEnv m, HasHermitMEnv m, MonadIO m, MonadThings m)
                => NameSpace -> String -> c -> m Named
findInNameSpace ns nm c =
    case filter ((== ns) . occNameSpace . getOccName) $ varSetElems (findBoundVars nm c) of
        _ : _ : _ -> fail "multiple matching variables in scope."
        [v]       -> return $ varToNamed v
        []        -> findInNSModGuts ns (parseName nm)

-- | Looks for Named in current GlobalRdrEnv. If not present, calls 'findInNSPackageDB'.
findInNSModGuts :: (HasHscEnv m, HasHermitMEnv m, MonadIO m, MonadThings m)
                => NameSpace -> HermitName -> m Named
findInNSModGuts ns nm = do
    rdrEnv <- liftM mg_rdr_env getModGuts
    case lookupGRE_RdrName (toRdrName ns nm) rdrEnv of
        [gre] -> nameToNamed $ gre_name gre
        []    -> findInNSPackageDB ns nm
        _     -> fail "findInNSModGuts: multiple names returned"

-- | Looks for Named in package database, or built-in packages.
findInNSPackageDB :: (HasHscEnv m, HasHermitMEnv m, MonadIO m, MonadThings m)
                  => NameSpace -> HermitName -> m Named
findInNSPackageDB ns nm = do
    mnm <- lookupName ns nm
    case mnm of
        Nothing -> findNamedBuiltIn ns (hnUnqualified nm)
        Just n  -> nameToNamed n

-- | Helper to call GHC's lookupRdrNameInModuleForPlugins
lookupName :: (HasHermitMEnv m, HasHscEnv m, MonadIO m) => NameSpace -> HermitName -> m (Maybe Name)
lookupName ns nm = case isQual_maybe rdrName of
                    Nothing    -> return Nothing -- we can't use lookupName on the current module
                    Just (m,_) -> do
                        hscEnv <- getHscEnv
                        guts <- getModGuts
                        liftIO $ lookupRdrNameInModuleForPlugins hscEnv guts m rdrName
    where rdrName = toRdrName ns nm

-- | Looks for Named amongst GHC's built-in DataCons/TyCons.
findNamedBuiltIn :: Monad m => NameSpace -> String -> m Named
findNamedBuiltIn ns str
    | isValNameSpace ns =
        case [ dc | tc <- wiredInTyCons, dc <- tyConDataCons tc, str == getOccString dc ] of
            [] -> fail "name not in scope."
            [dc] -> return $ NamedDataCon dc
            dcs -> fail $ "multiple DataCons match: " ++ show (map getOccString dcs)
    | isTcClsNameSpace ns =
        case [ tc | tc <- wiredInTyCons, str == getOccString tc ] of
            [] -> fail "type name not in scope."
            [tc] -> return $ NamedTyCon tc
            tcs -> fail $ "multiple TyCons match: " ++ show (map getOccString tcs)
    | otherwise = fail "findNameBuiltIn: unusable NameSpace"

-- | We have a name, find the corresponding Named.
nameToNamed :: MonadThings m => Name -> m Named
nameToNamed n | isVarName n     = liftM NamedId $ lookupId n
              | isDataConName n = liftM NamedDataCon $ lookupDataCon n
              | isTyConName n   = liftM NamedTyCon $ lookupTyCon n
              | isTyVarName n   = fail "nameToNamed: impossible, TyVars are not exported and cannot be looked up."
              | otherwise       = fail "nameToNamed: unknown name type"

#else

-- | Looks for Id with given name in the context. If it is not present, calls 'findIdMG'.
findId :: (BoundVars c, HasHermitMEnv m, HasHscEnv m, MonadCatch m, MonadIO m, MonadThings m) => String -> c -> m Id
findId nm c = case varSetElems (findBoundVars nm c) of
                []         -> findIdMG (parseName nm)
                [v]        -> return v
                _ : _ : _  -> fail "multiple matching variables in scope."

findIdMG :: (HasHermitMEnv m, MonadThings m) => HermitName -> m Id
findIdMG hnm = do
    let nm = hnUnqualified hnm
    rdrEnv <- liftM mg_rdr_env getModGuts
    case filter isValName $ findNamesFromString rdrEnv nm of
        []  -> findIdBuiltIn nm
        [n] -> nameToId n
        ns  -> fail $ "multiple matches found:\n" ++ intercalate ", " (map getOccString ns)

-- | We have a name, find the corresponding Id.
nameToId :: MonadThings m => Name -> m Id
nameToId n | isVarName n     = lookupId n
           | isDataConName n = liftM dataConWrapId $ lookupDataCon n
           | otherwise       = fail "nameToId: unknown name type"

findIdBuiltIn :: forall m. Monad m => String -> m Id
findIdBuiltIn = go
    where go ":"     = dataConId consDataCon
          go "[]"    = dataConId nilDataCon

          go "True"  = return trueDataConId
          go "False" = return falseDataConId

          go "<"     = return ltDataConId
          go "=="    = return eqDataConId
          go ">"     = return gtDataConId

          go "I#"    = dataConId intDataCon

          go "()"    = return unitDataConId
          -- TODO: add more as needed
          --       http://www.haskell.org/ghc/docs/latest/html/libraries/ghc/TysWiredIn.html
          go _   = fail "variable not in scope."

          dataConId :: DataCon -> m Id
          dataConId = return . dataConWorkId
#endif

-- Someday, when Applicative is a superclass of monad, we can uncomment the
-- nicer applicative definitions. For now, we don't want the extra constraint.

-- | Make a 'Name' from a string.
newName :: MonadUnique m => String -> m Name
newName nm = getUniqueM >>= return . flip mkSystemVarName (mkFastString nm)
-- newName nm = mkSystemVarName <$> getUniqueM <*> pure (mkFastString nm)

-- | Make a unique global identifier for a specified type, using a provided name.
newGlobalIdH :: MonadUnique m => String -> Type -> m Id
newGlobalIdH nm ty = newName nm >>= return . flip mkVanillaGlobal ty
-- newGlobalIdH nm ty = mkVanillaGlobal <$> newName nm <*> pure ty

-- | Make a unique identifier for a specified type, using a provided name.
newIdH :: MonadUnique m => String -> Type -> m Id
newIdH nm ty = newName nm >>= return . flip mkLocalId ty
-- newIdH nm ty = mkLocalId <$> newName nm <*> pure ty

-- | Make a unique type variable for a specified kind, using a provided name.
newTyVarH :: MonadUnique m => String -> Kind -> m TyVar
newTyVarH nm k = newName nm >>= return . flip mkTyVar k
-- newTyVarH nm k = mkTyVar <$> newName nm <*> pure k

-- | Make a unique coercion variable for a specified type, using a provided name.
newCoVarH :: MonadUnique m => String -> Type -> m TyVar
newCoVarH nm ty = newName nm >>= return . flip mkCoVar ty
-- newCoVarH nm ty = mkCoVar <$> newName nm <*> pure ty

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
    name = nameMod (uqName v)
    ty   = varType v
