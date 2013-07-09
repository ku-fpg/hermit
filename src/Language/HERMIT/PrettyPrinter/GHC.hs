-- | Output the raw Expr constructors. Helpful for writing pattern matching rewrites.
module Language.HERMIT.PrettyPrinter.GHC
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

import qualified GhcPlugins as GHC
import Language.HERMIT.Kure
import Language.HERMIT.Core
import Language.HERMIT.PrettyPrinter.Common

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
ppSDoc :: GHC.Outputable a => PrettyH a
ppSDoc = do dynFlags <- constT GHC.getDynFlags
            arr (toDoc . GHC.showPpr dynFlags)
    where toDoc s | any isSpace s = parens (text s)
                  | otherwise     = text s

ppModGuts :: PrettyH GHC.ModGuts
ppModGuts = GHC.mg_binds ^>> ppSDoc

ppCoreProg :: PrettyH CoreProg
ppCoreProg = progToBinds ^>> ppSDoc

ppCoreExpr :: PrettyH GHC.CoreExpr
ppCoreExpr = ppSDoc

ppCoreBind :: PrettyH GHC.CoreBind
ppCoreBind = ppSDoc

ppCoreAlt :: PrettyH GHC.CoreAlt
ppCoreAlt = ppSDoc

ppCoreDef :: PrettyH CoreDef
ppCoreDef = defT ppSDoc ppCoreExpr $ \ i e -> i <+> char '=' <+> e

ppKindOrType :: PrettyH GHC.Type
ppKindOrType = ppSDoc

ppCoercion :: PrettyH GHC.Coercion
ppCoercion = ppSDoc

---------------------------------------------------------------------------
