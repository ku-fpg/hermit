{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ <= 706
{-# LANGUAGE ScopedTypeVariables #-}
#endif
module HERMIT.Name
    ( HermitName
    , fromRdrName
    , toRdrName
    , toRdrNames
    , hnModuleName
    , hnUnqualified
    , parseName
      -- * Namespaces
    , Named(..)
    , varToNamed
    , allNameSpaces
    , dataConNS
    , tyConClassNS
    , tyVarNS
    , varNS
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

import HERMIT.Context
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad

-- | A 'HermitName' is an optionally fully-qualified name,
-- like GHC's 'RdrName', but without specifying which 'NameSpace'
-- the name is found in.
data HermitName = HermitName { hnModuleName  :: Maybe ModuleName
                             , hnUnqualified :: String
                             }

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

mkQualified :: String -> String -> HermitName
mkQualified mnm nm = HermitName (Just $ mkModuleName mnm) nm
-- mkOccName
-- mkRdrQual

mkUnqualified :: String -> HermitName
mkUnqualified = HermitName Nothing
-- mkRdrUnqual

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

-- | Parse a HermitName from a String.
parseName :: String -> HermitName
parseName s | isQualified s = parseQualified s
            | otherwise     = mkUnqualified s

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
