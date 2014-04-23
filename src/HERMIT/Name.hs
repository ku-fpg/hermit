{-# LANGUAGE CPP #-}
module HERMIT.Name 
    ( HermitName
    , fromRdrName
    , toRdrName
    , toRdrNames
    , hnModuleName
    , hnUnqualified
    , parseName
#if __GLASGOW_HASKELL__ > 706
    , lookupName
#endif
      -- * Namespaces
    , allNameSpaces
    , dataConNS
    , tyConClassNS
    , tyVarNS
    , varNS
    ) where

#if __GLASGOW_HASKELL__ > 706
import Control.Monad.IO.Class
import HERMIT.Monad
#endif

import HERMIT.GHC

-- | A 'HermitName' is an optionally fully-qualified name,
-- like GHC's 'RdrName', but without specifying which 'NameSpace'
-- the name is found in.
data HermitName = HermitName { hnModuleName  :: Maybe ModuleName
                             , hnUnqualified :: String 
                             }

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

#if __GLASGOW_HASKELL__ > 706
lookupName :: (HasModGuts m, HasHscEnv m, MonadIO m) => NameSpace -> HermitName -> m (Maybe Name)
lookupName ns nm = case isQual_maybe rdrName of
                    Nothing    -> return Nothing -- we can't use lookupName on the current module
                    Just (m,_) -> do
                        hscEnv <- getHscEnv
                        guts <- getModGuts
                        liftIO $ lookupRdrNameInModuleForPlugins hscEnv guts m rdrName
    where rdrName = toRdrName ns nm
#endif
