-- | Output the raw Expr constructors. Helpful for writing pattern matching rewrites.
module HERMIT.PrettyPrinter.GHC
  ( -- * GHC's standard Pretty-Printer for GHC Core
    externals
  , pretty
  , ppCoreTC
  , ppModGuts
  , ppCoreProg
  , ppCoreBind
  , ppCoreExpr
  , ppCoreAlt
  , ppKindOrType
  , ppCoercion
  )
where

import Control.Arrow hiding ((<+>))

import Data.Char (isSpace)
import Data.Default.Class

import HERMIT.Core
import HERMIT.External
import HERMIT.GHC hiding ((<+>), (<>), char, text, parens, hsep, empty)
import HERMIT.Kure

import HERMIT.PrettyPrinter.Common

import Text.PrettyPrint.MarkedHughesPJ as PP

---------------------------------------------------------------------------

externals :: [External]
externals = [ external "ghc" pretty ["GHC pretty printer."] ]

pretty :: PrettyPrinter
pretty = PP { pLCoreTC = promoteT ppCoreTC -- TODO
            , pOptions = def
            , pTag = "ghc"
            }

-- | This pretty printer is just a reflection of GHC's standard pretty printer.
ppCoreTC :: PrettyH CoreTC
ppCoreTC =
          promoteExprT     ppCoreExpr
       <+ promoteProgT     ppCoreProg
       <+ promoteBindT     ppCoreBind
       <+ promoteDefT      ppCoreDef
       <+ promoteModGutsT  ppModGuts
       <+ promoteAltT      ppCoreAlt
       <+ promoteTypeT     ppKindOrType
       <+ promoteCoercionT ppCoercion

-- Use for any GHC structure.
ppSDoc :: Outputable a => PrettyH a
ppSDoc = do dynFlags <- constT getDynFlags
            arr (toDoc . showPpr dynFlags)
    where toDoc s | any isSpace s = parens (text s)
                  | otherwise     = text s

ppModGuts :: PrettyH ModGuts
ppModGuts = mg_binds ^>> ppSDoc

ppCoreProg :: PrettyH CoreProg
ppCoreProg = progToBinds ^>> ppSDoc

ppCoreExpr :: PrettyH CoreExpr
ppCoreExpr = ppSDoc

ppCoreBind :: PrettyH CoreBind
ppCoreBind = ppSDoc

ppCoreAlt :: PrettyH CoreAlt
ppCoreAlt = ppSDoc

ppCoreDef :: PrettyH CoreDef
ppCoreDef = defT ppSDoc ppCoreExpr $ \ i e -> i <+> char '=' <+> e

ppKindOrType :: PrettyH Type
ppKindOrType = ppSDoc

ppCoercion :: PrettyH Coercion
ppCoercion = ppSDoc

{- TODO: lemma pp for GHC-style
ppForallQuantification :: PrettyH [Var]
ppForallQuantification =
  do vs <- mapT ppSDoc
     if null vs
     then return empty
     else return $ text "forall" <+> hsep vs <> text "."
-}

---------------------------------------------------------------------------
