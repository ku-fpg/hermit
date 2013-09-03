-- | Output the raw Expr constructors. Helpful for writing pattern matching rewrites.
module HERMIT.PrettyPrinter.GHC
  ( -- * GHC's standard Pretty-Printer for GHC Core
    ppCoreTC
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

import HERMIT.Kure
import HERMIT.Core
import HERMIT.GHC hiding ((<+>), char, text, parens)
import HERMIT.PrettyPrinter.Common

import Text.PrettyPrint.MarkedHughesPJ as PP

---------------------------------------------------------------------------

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

---------------------------------------------------------------------------
