-- | Output the raw Expr constructors. Helpful for writing pattern matching rewrites.
module Language.HERMIT.PrettyPrinter.GHC where

import Control.Arrow hiding ((<+>))

import Data.Char (isSpace)

import qualified GhcPlugins as GHC
import Language.HERMIT.HermitKure
import Language.HERMIT.PrettyPrinter

import Text.PrettyPrint.MarkedHughesPJ as PP

listify :: (MDoc a -> MDoc a -> MDoc a) -> [MDoc a] -> MDoc a
listify _  []     = text "[]"
listify op (d:ds) = op (text "[ " <> d) (foldr (\e es -> op (text ", " <> e) es) (text "]") ds)

-- | like vcat and hcat, only make the list syntax explicit
vlist, hlist :: [MDoc a] -> MDoc a
vlist = listify ($$)
hlist = listify (<+>)

corePrettyH :: PrettyOptions -> PrettyH Core
corePrettyH opts =
       promoteT (ppCoreExpr :: PrettyH GHC.CoreExpr)
    <+ promoteT (ppProgram  :: PrettyH GHC.CoreProgram)
    <+ promoteT (ppCoreBind :: PrettyH GHC.CoreBind)
    <+ promoteT (ppCoreDef  :: PrettyH CoreDef)
    <+ promoteT (ppModGuts  :: PrettyH GHC.ModGuts)
    <+ promoteT (ppCoreAlt  :: PrettyH GHC.CoreAlt)
  where
    hideNotes = po_notes opts

    -- Only use for base types!  -- Not used anywhere?
    ppShow :: (Show a) => a -> MDoc b
    ppShow = text . show

    -- Use for any GHC structure, the 'showSDoc' prefix is to remind us
    -- that we are eliding infomation here.
    ppSDoc :: (GHC.Outputable a) => a -> MDoc b
    ppSDoc = toDoc . (if hideNotes then id else ("showSDoc: " ++)) . GHC.showSDoc . GHC.ppr
        where toDoc s | any isSpace s = parens (text s)
                      | otherwise     = text s

    ppModGuts :: PrettyH GHC.ModGuts
    ppModGuts = arr (ppSDoc . GHC.mg_binds)

    -- DocH is not a monoid, so we can't use listT here
    ppProgram :: PrettyH GHC.CoreProgram
    ppProgram = arr ppSDoc

    ppCoreExpr :: PrettyH GHC.CoreExpr
    ppCoreExpr = arr ppSDoc

    ppCoreBind :: PrettyH GHC.CoreBind
    ppCoreBind = arr ppSDoc

    ppCoreAlt :: PrettyH GHC.CoreAlt
    ppCoreAlt = arr ppSDoc

    -- GHC uses a tuple, which we print here. The CoreDef type is our doing.
    ppCoreDef :: PrettyH CoreDef
    ppCoreDef = defT ppCoreExpr $ \ i e -> ppSDoc i <> text "=" <> e
