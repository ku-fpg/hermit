-- | Output the raw Expr constructors. Helpful for writing pattern matching rewrites.
module Language.HERMIT.PrettyPrinter.GHC
  ( -- * GHC's standard Pretty-Printer for GHC Core
    corePrettyH
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
corePrettyH :: PrettyH CoreTC
corePrettyH = do
    dynFlags <- constT GHC.getDynFlags

    let

        -- Use for any GHC structure, the 'showSDoc' prefix is to remind us
        -- that we are eliding infomation here.
        ppSDoc :: (GHC.Outputable a) => a -> MDoc b
        ppSDoc = toDoc . GHC.showSDoc dynFlags . GHC.ppr
            where toDoc s | any isSpace s = parens (text s)
                          | otherwise     = text s

        ppModGuts :: PrettyH GHC.ModGuts
        ppModGuts = arr (ppSDoc . GHC.mg_binds)

        ppCoreProg :: PrettyH CoreProg
        ppCoreProg = arr (ppSDoc . progToBinds)

        ppCoreExpr :: PrettyH GHC.CoreExpr
        ppCoreExpr = arr ppSDoc

        ppCoreBind :: PrettyH GHC.CoreBind
        ppCoreBind = arr ppSDoc

        ppCoreAlt :: PrettyH GHC.CoreAlt
        ppCoreAlt = arr ppSDoc

        ppCoreDef :: PrettyH CoreDef
        ppCoreDef = defT (arr ppSDoc) ppCoreExpr $ \ i e -> i <+> text "=" <+> e

        ppType :: PrettyH GHC.Type
        ppType = arr ppSDoc

        ppCoercion :: PrettyH GHC.Coercion
        ppCoercion = arr ppSDoc

    promoteT (ppCoreExpr :: PrettyH GHC.CoreExpr)
     <+ promoteT (ppCoreProg :: PrettyH CoreProg)
     <+ promoteT (ppCoreBind :: PrettyH GHC.CoreBind)
     <+ promoteT (ppCoreDef  :: PrettyH CoreDef)
     <+ promoteT (ppModGuts  :: PrettyH GHC.ModGuts)
     <+ promoteT (ppCoreAlt  :: PrettyH GHC.CoreAlt)
     <+ promoteT (ppType     :: PrettyH GHC.Type)
     <+ promoteT (ppCoercion :: PrettyH GHC.Coercion)

---------------------------------------------------------------------------
