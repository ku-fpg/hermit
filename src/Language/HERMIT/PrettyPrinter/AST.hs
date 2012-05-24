-- | Output the raw Expr constructors. Helpful for writing pattern matching rewrites.
module Language.HERMIT.PrettyPrinter.AST where

import Data.Traversable (sequenceA)

import qualified GhcPlugins as GHC
import Language.HERMIT.HermitKure
import Language.HERMIT.PrettyPrinter
import Language.KURE

import Text.PrettyPrint.MarkedHughesPJ as PP

astCorePrettyH :: Bool -> PrettyH Core
astCorePrettyH hideNotes =
       promoteT (ppCoreExpr :: PrettyH GHC.CoreExpr)
    <+ promoteT (ppProgram  :: PrettyH GHC.CoreProgram)
    <+ promoteT (ppCoreBind :: PrettyH GHC.CoreBind)
    <+ promoteT (ppCoreDef  :: PrettyH CoreDef)
    <+ promoteT (ppModGuts  :: PrettyH GHC.ModGuts)
    <+ promoteT (ppCoreAlt  :: PrettyH GHC.CoreAlt)
  where
    -- Only use for base types!
    ppShow :: (Show a) => a -> MDoc b
    ppShow = text . show

    -- Use for any GHC structure, the 'showSDoc' prefix is to remind us
    -- that we are eliding infomation here.
    ppSDoc :: (GHC.Outputable a) => a -> MDoc b
    ppSDoc = parens . text . (if hideNotes then id else ("showSDoc: " ++)) . GHC.showSDoc . GHC.ppr

    -- | @prePunctuate p [d1, ... dn] = [d1, p \<> d2, ... p \<> dn-1, p \<> dn]@
    listify :: [MDoc a] -> MDoc a
    listify []     = text "[]"
    listify (d:ds) = text "[ " <> d $$ (foldr (\e es -> text ", " <> e $$ es) (text "]") ds)

    ppModGuts :: PrettyH GHC.ModGuts
    ppModGuts = liftT (ppSDoc . GHC.mg_module)

    -- DocH is not a monoid, so we can't use listT here
    ppProgram :: PrettyH GHC.CoreProgram
    ppProgram = translate $ \ c -> fmap vcat . sequenceA . map (apply ppCoreBind c)

    ppCoreExpr :: PrettyH GHC.CoreExpr
    ppCoreExpr = varT (\i -> text "Var" <+> ppSDoc i)
              <+ litT (\i -> text "Lit" <+> ppSDoc i)
              <+ appT ppCoreExpr ppCoreExpr (\ a b -> text "App" $$ nest 2 (cat [parens a, parens b]))
              <+ lamT ppCoreExpr (\ v e -> text "Lam" <+> ppSDoc v $$ nest 2 (parens e))
              <+ letT ppCoreBind ppCoreExpr (\ b e -> text "Let" $$ nest 2 (cat [parens b, parens e]))
              <+ caseT ppCoreExpr (const ppCoreAlt) (\s b ty alts ->
                        text "Case" $$ nest 2 (parens s)
                                    $$ nest 2 (ppSDoc b)
                                    $$ nest 2 (ppSDoc ty)
                                    $$ nest 2 (listify (map parens alts)))
              <+ castT ppCoreExpr (\e co -> text "Cast" $$ nest 2 ((parens e) <+> ppSDoc co))
              <+ tickT ppCoreExpr (\i e  -> text "Tick" $$ nest 2 (ppSDoc i <+> parens e))
              <+ typeT (\ty -> text "Type" $$ nest 2 (ppSDoc ty))
              <+ coercionT (\co -> text "Coercion" $$ nest 2 (ppSDoc co))

    ppCoreBind :: PrettyH GHC.CoreBind
    ppCoreBind = nonRecT ppCoreExpr (\i e -> text "NonRec" <+> ppSDoc i $$ nest 2 (parens e))
              <+ recT (const ppCoreDef) (\bnds -> text "Rec" $$ nest 2 (vcat $ map parens bnds))

    ppCoreAlt :: PrettyH GHC.CoreAlt
    ppCoreAlt = altT ppCoreExpr $ \ con ids e -> text "Alt" <+> ppSDoc con
                                                            <+> (hsep $ map ppSDoc ids)
                                                            $$ nest 2 (parens e)

    -- GHC uses a tuple, which we print here. The CoreDef type is our doing.
    ppCoreDef :: PrettyH CoreDef
    ppCoreDef = defT ppCoreExpr $ \ i e -> parens $ ppSDoc i <> text "," <> e
