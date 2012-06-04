module Language.HERMIT.Primitive.Consider where

import GhcPlugins as GHC
import Convert

import Data.List
import Data.Monoid

import Language.HERMIT.HermitKure
import Language.HERMIT.External
import Language.HERMIT.HermitEnv
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
consider nm = do First cxtpaths <- tdpruneT $ promoteT $ findPathTo nm
                 case cxtpaths of
                   Just cxtpath -> rmPrefix cxtpath >>= pathL
                   Nothing      -> failNameNotFound nm

-- Take a ContextPath (always from the *Root*) from a deeper location,
-- and return the Path to *this* node.
rmPrefix :: ContextPath -> TranslateH Core Path
rmPrefix (ContextPath path) = do ContextPath this <- pathT
                                 guardFail (this `isSuffixOf` path) "rmPrefix failure"
                                 return $ drop (length this) $ reverse path

findPathTo :: TH.Name -> TranslateH CoreBind (First ContextPath)
findPathTo nm = translate $ \ c e -> let p = return $ First $ Just $ hermitBindingPath c in
        case e of
          NonRec v _ | nm `cmpName` idName v                            -> p
          Rec bds    | [ _ ] <- filter (cmpName nm . idName . fst) bds  -> p
          _                                                             -> failNameNotFound nm

failNameNotFound :: Monad m => TH.Name -> m a
failNameNotFound nm = fail $ "Name \"" ++ show nm ++ "\" not found."

-- Hacks till we can find the correct way of doing these.
cmpName :: TH.Name -> Name -> Bool
cmpName = cmpTHName2Name

var :: TH.Name -> RewriteH CoreExpr
var nm = contextfreeT $ \ e -> do
  liftIO $ print ("VAR",GHC.showSDoc . GHC.ppr $ thRdrNameGuesses $ nm)
  case e of
    Var n0 | nm `cmpName` idName n0 -> return e
    _                               -> failNameNotFound nm
