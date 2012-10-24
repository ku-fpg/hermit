-- | Output the raw Expr constructors. Helpful for writing pattern matching rewrites.
module Language.HERMIT.PrettyPrinter.AST where

import Control.Arrow hiding ((<+>))

import Data.Char (isSpace)
import Data.Traversable (sequenceA)

import qualified GhcPlugins as GHC
import Language.HERMIT.Kure
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
corePrettyH opts = do
    dynFlags <- constT GHC.getDynFlags

    let hideNotes = po_notes opts

        -- Use for any GHC structure, the 'showSDoc' prefix is to remind us
        -- that we are eliding infomation here.
        ppSDoc :: (GHC.Outputable a) => a -> MDoc b
        ppSDoc = toDoc . (if hideNotes then id else ("showSDoc: " ++)) . GHC.showSDoc dynFlags . GHC.ppr
            where toDoc s | any isSpace s = parens (text s)
                          | otherwise     = text s

        ppModGuts :: PrettyH GHC.ModGuts
        ppModGuts = arr (ppSDoc . GHC.mg_module)

        -- DocH is not a monoid.
        -- GHC uses a list, which we print here. The CoreProg type is our doing.
        ppCoreProg :: PrettyH CoreProg
        ppCoreProg = translate $ \ c -> fmap vlist . sequenceA . map (apply ppCoreBind c) . progToBinds

        ppCoreExpr :: PrettyH GHC.CoreExpr
        ppCoreExpr = varT (\i -> text "Var" <+> varColor (ppSDoc i))
                  <+ litT (\i -> text "Lit" <+> ppSDoc i)
                  <+ appT ppCoreExpr ppCoreExpr (\ a b -> text "App" $$ nest 2 (cat [parens a, parens b]))
                  <+ lamT ppCoreExpr (\ v e -> text "Lam" <+> varColor (ppSDoc v) $$ nest 2 (parens e))
                  <+ letT ppCoreBind ppCoreExpr (\ b e -> text "Let" $$ nest 2 (cat [parens b, parens e]))
                  <+ caseT ppCoreExpr (const ppCoreAlt) (\s b ty alts ->
                            text "Case" $$ nest 2 (parens s)
                                        $$ nest 2 (ppSDoc b)
                                        $$ nest 2 (ppSDoc ty)
                                        $$ nest 2 (vlist alts))
                  <+ castT ppCoreExpr (\e co -> text "Cast" $$ nest 2 ((parens e) <+> ppSDoc co))
                  <+ tickT ppCoreExpr (\i e  -> text "Tick" $$ nest 2 (ppSDoc i <+> parens e))
                  <+ typeT (\ty -> text "Type" <+> nest 2 (ppSDoc ty))
                  <+ coercionT (\co -> text "Coercion" $$ nest 2 (ppSDoc co))

        ppCoreBind :: PrettyH GHC.CoreBind
        ppCoreBind = nonRecT ppCoreExpr (\i e -> text "NonRec" <+> ppSDoc i $$ nest 2 (parens e))
                  <+ recT (const ppCoreDef) (\bnds -> text "Rec" $$ nest 2 (vlist bnds))

        ppCoreAlt :: PrettyH GHC.CoreAlt
        ppCoreAlt = altT ppCoreExpr $ \ con ids e -> text "Alt" <+> ppSDoc con
                                                                <+> (hlist $ map ppSDoc ids)
                                                                $$ nest 2 (parens e)

        -- GHC uses a tuple, which we print here. The CoreDef type is our doing.
        ppCoreDef :: PrettyH CoreDef
        ppCoreDef = defT ppCoreExpr $ \ i e -> parens $ varColor (ppSDoc i) <> text "," <> e

    promoteT (ppCoreExpr :: PrettyH GHC.CoreExpr)
     <+ promoteT (ppCoreProg :: PrettyH CoreProg)
     <+ promoteT (ppCoreBind :: PrettyH GHC.CoreBind)
     <+ promoteT (ppCoreDef  :: PrettyH CoreDef)
     <+ promoteT (ppModGuts  :: PrettyH GHC.ModGuts)
     <+ promoteT (ppCoreAlt  :: PrettyH GHC.CoreAlt)
