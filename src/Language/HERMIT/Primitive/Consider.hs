module Language.HERMIT.Primitive.Consider where

import GhcPlugins as GHC
-- import Convert

import Language.HERMIT.HermitKure
import Language.HERMIT.External
import Language.HERMIT.GHC

import qualified Language.Haskell.TH as TH

externals :: [External]
externals = map (.+ Lens)
            [
              external "consider" consider
                [ "'consider <v>' focuses into a named binding <v>" ]
        -- This is in the wrong place
            , external "var" (promoteR . var :: TH.Name -> RewriteH Core)
                [ "var <v> succeeded for variable v, and fails otherwise"]
            ]

-- Focus on a bindings
consider :: TH.Name -> LensH Core Core
consider = joinTL . fmap pathL . uniquePathToT . nameBound

nameBound :: TH.Name -> Core -> Bool
nameBound nm (BindCore (NonRec v _))  =  nm `cmpName` idName v
nameBound nm (BindCore (Rec bds))     =  any (cmpName nm . idName) $ map fst bds
nameBound _  _                        =  False

-- Hacks till we can find the correct way of doing these.
cmpName :: TH.Name -> Name -> Bool
cmpName = cmpTHName2Name


var :: TH.Name -> RewriteH CoreExpr
var nm = whenM (varT $ \ v -> nm `cmpName` idName v) idR

-- var nm = contextfreeT $ \ e -> do
--   liftIO $ print ("VAR",GHC.showSDoc . GHC.ppr $ thRdrNameGuesses $ nm)
--   case e of
--     Var n0 | nm `cmpName` idName n0 -> return e
--     _                               -> fail $ "Name \"" ++ show nm ++ "\" not found."
