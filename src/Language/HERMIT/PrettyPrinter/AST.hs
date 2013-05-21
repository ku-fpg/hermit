{-# LANGUAGE CPP #-}

-- | Output the raw Expr constructors. Helpful for writing pattern matching rewrites.
module Language.HERMIT.PrettyPrinter.AST
  ( -- * HERMIT's AST Pretty-Printer for GHC Core
    corePrettyH
  )
where

import Control.Arrow hiding ((<+>))

import Data.Char (isSpace)
import Data.Traversable (sequenceA)

import GhcPlugins (Coercion(..), Var(..), Id, CoVar)
import qualified GhcPlugins as GHC

import Language.HERMIT.GHC
import Language.HERMIT.Kure
import Language.HERMIT.Core
import Language.HERMIT.PrettyPrinter.Common

import Text.PrettyPrint.MarkedHughesPJ as PP

---------------------------------------------------------------------------

-- | Pretty print a fragment of GHC Core using HERMIT's \"AST\" pretty printer.
--   This displays the tree of constructors using nested indentation.
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
        ppCoreExpr = varT (\i -> text "Var" <+> ppId i)
                  <+ litT (\i -> text "Lit" <+> ppSDoc i)
                  <+ appT ppCoreExpr ppCoreExpr (\ a b -> text "App" $$ nest 2 (cat [parens a, parens b]))
                  <+ lamT ppCoreExpr (\ v e -> text "Lam" <+> ppVar v $$ nest 2 (parens e))
                  <+ letT ppCoreBind ppCoreExpr (\ b e -> text "Let" $$ nest 2 (cat [parens b, parens e]))
                  <+ caseT ppCoreExpr (const ppCoreAlt) (\s b ty alts ->
                            text "Case" $$ nest 2 (parens s)
                                        $$ nest 2 (ppSDoc b)
                                        $$ nest 2 (ppTypeColParen ty)
                                        $$ nest 2 (vlist alts))
                  <+ castT ppCoreExpr (\e co -> text "Cast" $$ nest 2 (parens e <+> ppCoercionColParen co))
                  <+ tickT ppCoreExpr (\i e  -> text "Tick" $$ nest 2 (ppSDoc i <+> parens e))
                  <+ typeT (\ ty -> text "Type" $$ nest 2 (ppTypeColParen ty))
                  <+ coercionT (\ co -> text "Coercion" $$ nest 2 (ppCoercionColParen co))

        ppCoreBind :: PrettyH GHC.CoreBind
        ppCoreBind = nonRecT ppCoreExpr (\ v e -> text "NonRec" <+> ppVar v $$ nest 2 (parens e))
                  <+ recT (const ppCoreDef) (\bnds -> text "Rec" $$ nest 2 (vlist bnds))

        ppCoreAlt :: PrettyH GHC.CoreAlt
        ppCoreAlt = altT ppCoreExpr $ \ con vs e -> text "Alt" <+> ppSDoc con
                                                               <+> (hlist $ map ppVar vs)
                                                               $$ nest 2 (parens e)

        -- GHC uses a tuple, which we print here. The CoreDef type is our doing.
        ppCoreDef :: PrettyH CoreDef
        ppCoreDef = defT ppCoreExpr $ \ i e -> parens $ ppId i <> text "," <> e

        ppTypeColParen :: Type -> DocH
        ppTypeColParen = typeColor . parens . ppCoreType

        ppCoreType :: Type -> DocH
        ppCoreType (TyVarTy v)     = text "TyVarTy" <+> ppTyVar v
        ppCoreType (LitTy tylit)   = text "LitTy" <+> ppSDoc tylit
        ppCoreType (AppTy ty1 ty2) = text "AppTy" $$ nest 2 (cat $ map (parens.ppCoreType) [ty1, ty2])
        ppCoreType (FunTy ty1 ty2) = let a = ppCoreType ty1
                                         b = ppCoreType ty2
                                      in text "FunTy" $$ nest 2 (cat [parens a, parens b])
        ppCoreType (ForAllTy v ty) = text "ForAllTy" <+> ppTyVar v $$ nest 2 (parens $ ppCoreType ty)
        ppCoreType (TyConApp tyCon tys) = text "TyConApp" <+> ppSDoc tyCon $$ nest 2 (vlist $ map ppCoreType tys)

        ppCoercionColParen :: Coercion -> DocH
        ppCoercionColParen = coercionColor . parens . ppCoreCoercion

        ppCoreCoercion :: Coercion -> DocH
        ppCoreCoercion (Refl ty)           = text "Refl" $$ nest 2 (ppTypeColParen ty)
        ppCoreCoercion (CoVarCo v)         = text "CoVarCo" <+> ppCoVar v
        ppCoreCoercion (SymCo co)          = text "SymCo" $$ nest 2 (parens $ ppCoreCoercion co)
        ppCoreCoercion (AppCo co1 co2)     = text "AppCo" $$ nest 2 (cat $ map (parens.ppCoreCoercion) [co1, co2])
        ppCoreCoercion (ForAllCo v co)     = text "ForAllCo" <+> ppCoVar v $$ nest 2 (parens $ ppCoreCoercion co)
        ppCoreCoercion (TransCo co1 co2)   = text "TransCo" $$ nest 2 (cat $ map (parens.ppCoreCoercion) [co1, co2])
        ppCoreCoercion (TyConAppCo con cs) = text "TyConAppCo" <+> ppSDoc con $$ nest 2 (vlist $ map ppCoreCoercion cs)
        ppCoreCoercion (UnsafeCo t1 t2)    = text "UnsafeCo" $$ nest 2 (cat $ map ppTypeColParen [t1, t2])
        ppCoreCoercion (NthCo n co)        = text "NthCo" <+> text (show n) $$ (parens $ ppCoreCoercion co)
        ppCoreCoercion (InstCo co t)       = text "InstCo" $$ nest 2 (cat [parens (ppCoreCoercion co), ppTypeColParen t])
#if __GLASGOW_HASKELL__ > 706
        -- TODO: Figure out how to properly pp new branched Axioms and Left/Right Coercions
        ppCoreCoercion (AxiomInstCo ax idx cs) = text "AxiomInstCo" <+> ppSDoc ax <+> ppSDoc idx $$ nest 2 (vlist $ map ppCoreCoercion cs) -- TODO: add pretty printer for Coercion Axioms
        ppCoreCoercion (LRCo lr co) = text "LRCo" <+> ppSDoc lr $$ nest 2 (parens $ ppCoreCoercion co)
#else
        ppCoreCoercion (AxiomInstCo ax cs) = text "AxiomInstCo" <+> ppSDoc ax $$ nest 2 (vlist $ map ppCoreCoercion cs) -- TODO: add pretty printer for Coercion Axioms
#endif

        ppVar :: Var -> DocH
        ppVar v | GHC.isTyVar v = ppTyVar v
                | GHC.isCoVar v = ppCoVar v
                | otherwise     = ppId v

        ppId :: Id -> DocH
        ppId = idColor . ppSDoc

        ppTyVar :: Id -> DocH
        ppTyVar = typeColor . ppSDoc

        ppCoVar :: CoVar -> DocH
        ppCoVar = coercionColor . ppSDoc


    promoteT (ppCoreExpr :: PrettyH GHC.CoreExpr)
     <+ promoteT (ppCoreProg :: PrettyH CoreProg)
     <+ promoteT (ppCoreBind :: PrettyH GHC.CoreBind)
     <+ promoteT (ppCoreDef  :: PrettyH CoreDef)
     <+ promoteT (ppModGuts  :: PrettyH GHC.ModGuts)
     <+ promoteT (ppCoreAlt  :: PrettyH GHC.CoreAlt)

---------------------------------------------------------------------------
