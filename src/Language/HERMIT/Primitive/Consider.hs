module Language.HERMIT.Primitive.Consider where

import GhcPlugins as GHC

import Language.HERMIT.HermitKure
import Language.HERMIT.External
import Language.HERMIT.GHC

import Control.Arrow

import qualified Language.Haskell.TH as TH

externals :: [External]
externals = map (.+ Lens)
            [
              external "consider" consider
                [ "'consider <v>' focuses into a named binding <v>" ]
            , external "rhs-of" rhsOf
                [ "rhs-of 'name focuses into the right-hand-side of binding <v>" ]
        -- This is in the wrong place
            , external "var" (promoteR . var :: TH.Name -> RewriteH Core)
                [ "var <v> succeeded for variable v, and fails otherwise"]
            ]

-- Focus on a bindings
consider :: TH.Name -> TranslateH Core Path
consider = uniquePrunePathToT . bindGroup

-- find a bind group that defineds a given name

bindGroup :: TH.Name -> Core -> Bool
bindGroup nm (BindCore (NonRec v _))  =  nm `cmpName` idName v
bindGroup nm (BindCore (Rec bds))     =  any (cmpName nm . idName) $ map fst bds
bindGroup _  _                        =  False

-- find a specific binding's rhs.
rhsOf :: TH.Name -> TranslateH Core Path
rhsOf nm = uniquePrunePathToT (namedBinding nm) >>> arr (0 :)

namedBinding :: TH.Name -> Core -> Bool
namedBinding nm (BindCore (NonRec v _))  =  nm `cmpName` idName v
namedBinding nm (DefCore (Def v _))      =  nm `cmpName` idName v
namedBinding _  _                        =  False

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
