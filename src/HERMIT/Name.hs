module HERMIT.Name 
    ( HermitName
    , fromRdrName
    , toRdrName
    , toRdrNames
    , toUnqualified
    , parseName
    , lookupName
      -- * Namespaces
    , allNameSpaces
    , dataConNS
    , tyConClassNS
    , tyVarNS
    , varNS
    ) where

import Control.Monad.IO.Class

import HERMIT.GHC
import HERMIT.Monad

-- A wrapper around RdrName, in case we need to enrich later.
newtype HermitName = HermitName { toRdrName :: RdrName }

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

mkQualified :: NameSpace -> String -> String -> HermitName
mkQualified ns mnm nm = HermitName $ mkRdrQual (mkModuleName mnm) (mkOccName ns nm)

mkUnqualified :: NameSpace -> String -> HermitName
mkUnqualified ns = HermitName . mkRdrUnqual . mkOccName ns

fromRdrName :: RdrName -> HermitName
fromRdrName = HermitName

-- | Make a RdrName for each possible NameSpace.
toRdrNames :: HermitName -> [RdrName]
toRdrNames hnm = let nm = toRdrName hnm in [ setRdrNameSpace nm ns | ns <- allNameSpaces ]

parseQualified :: NameSpace -> String -> HermitName
parseQualified _ [] = error "parseQualified: empty string"
parseQualified ns s = mkQualified ns mnm nm
    where (c:cs) = reverse s -- we are careful to parse 'Prelude..' correctly
          (rNm, _dot:rMod) = break (=='.') cs
          (nm, mnm) = (reverse (c:rNm), reverse rMod)

-- | Parse a HermitName from a String.
parseName :: NameSpace -> String -> HermitName
parseName ns s | isQualified s = parseQualified ns s
               | otherwise     = mkUnqualified ns s

-- lookupRdrNameInModuleForPlugins :: HscEnv -> ModuleName -> RdrName -> IO (Maybe Name)

toUnqualified :: HermitName -> String
toUnqualified = occNameString . rdrNameOcc . toRdrName

lookupName :: (HasModGuts m, HasHscEnv m, MonadIO m) => HermitName -> m (Maybe Name)
lookupName nm = case isQual_maybe rdrName of
                    Nothing    -> return Nothing -- we can't use lookupName on the current module
                    Just (m,_) -> do
                        hscEnv <- getHscEnv
                        guts <- getModGuts
                        liftIO $ lookupRdrNameInModuleForPlugins hscEnv guts m rdrName
    where rdrName = toRdrName nm
