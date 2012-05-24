module Language.HERMIT.Primitive.Consider where

import GhcPlugins

import Data.List
import Data.Monoid

import Language.KURE

import Language.HERMIT.HermitKure
import Language.HERMIT.External
import Language.HERMIT.HermitEnv

import qualified Language.Haskell.TH as TH

externals :: [External]
externals = [
              external "consider" consider
                [ "'consider <v>' focuses into the rhs of the binding <v>" ]
            ]

-- Focus on the Rhs of a bindings
consider :: TH.Name -> LensH Core Core
consider nm = do First cxtpaths <- tdpruneT $ promoteT $ findPathTo nm
                 case cxtpaths of
                   Just cxtpath -> rmPrefix cxtpath >>= pathL
                   Nothing      -> failNameNotFound nm

-- Take a ContextPath (always from the *Root*) from a deeper location,
-- and return the Path to *this* node.
rmPrefix :: ContextPath -> TranslateH Core Path
rmPrefix (ContextPath path) = do ContextPath this <- pathT
                                 guardT (this `isSuffixOf` path) "rmPrefix failure"
                                 return $ drop (length this) $ reverse path

findPathTo :: TH.Name -> TranslateH CoreBind (First ContextPath)
findPathTo nm = translate $ \ c e -> let ContextPath ps = hermitBindingPath c in
        case e of
          NonRec v _ | nm `cmpName` idName v -> return $ First $ Just $ ContextPath (0 : ps)
          Rec bds -> let res = [ ContextPath (i : ps)
                               | ((v,_),i) <- zip bds [0..]
                               , nm `cmpName` idName v
                               ]
                      in case res of
                           [r] -> return $ First $ Just r
                           _   -> failNameNotFound nm
          _ -> failNameNotFound nm

failNameNotFound :: Monad m => TH.Name -> m a
failNameNotFound nm = fail $ "Name \"" ++ show nm ++ "\" not found."

-- Hacks till we can find the correct way of doing these.
cmpName :: TH.Name -> Name -> Bool
cmpName th_nm ghc_nm = TH.nameBase th_nm == occNameString (nameOccName ghc_nm)
