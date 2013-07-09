{-# LANGUAGE CPP #-}

-- | Output the raw Expr constructors. Helpful for writing pattern matching rewrites.
module Language.HERMIT.PrettyPrinter.AST
  ( -- * HERMIT's AST Pretty-Printer for GHC Core
    ppCoreTC
  , ppModGuts
  , ppCoreProg
  , ppCoreBind
  , ppCoreExpr
  , ppCoreAlt
  , ppType
  , ppCoercion
  )
where

import Control.Arrow hiding ((<+>))

import Data.Char (isSpace)

import GhcPlugins (Coercion(..), Var(..))
import qualified GhcPlugins as GHC

import Language.HERMIT.GHC
import Language.HERMIT.Kure
import Language.HERMIT.Core
import Language.HERMIT.PrettyPrinter.Common

import Text.PrettyPrint.MarkedHughesPJ as PP

---------------------------------------------------------------------------

coText :: String -> DocH
coText = coercionColor . text

tyText :: String -> DocH
tyText = typeColor . text

---------------------------------------------------------------------------

-- | Pretty print a fragment of GHC Core using HERMIT's \"AST\" pretty printer.
--   This displays the tree of constructors using nested indentation.
ppCoreTC :: PrettyH CoreTC
ppCoreTC =
          promoteExprT     ppCoreExpr
       <+ promoteProgT     ppCoreProg
       <+ promoteBindT     ppCoreBind
       <+ promoteDefT      ppCoreDef
       <+ promoteModGutsT  ppModGuts
       <+ promoteAltT      ppCoreAlt
       <+ promoteTypeT     ppType
       <+ promoteCoercionT ppCoercion

-- Use for any GHC structure, the 'showSDoc' prefix is to remind us
-- that we are eliding infomation here.
ppSDoc :: GHC.Outputable a => PrettyH a
ppSDoc =  do dynFlags <- constT GHC.getDynFlags
             hideNotes  <- (po_notes . prettyC_options) ^<< contextT
             arr (toDoc . (if hideNotes then id else ("showSDoc: " ++)) . GHC.showPpr dynFlags)
    where toDoc s | any isSpace s = parens (text s)
                  | otherwise     = text s

ppModGuts :: PrettyH GHC.ModGuts
ppModGuts =  GHC.mg_module ^>> ppSDoc

ppCoreProg :: PrettyH CoreProg
ppCoreProg = progConsT ppCoreBind ppCoreProg ($+$) <+ progNilT empty

ppCoreExpr :: PrettyH GHC.CoreExpr
ppCoreExpr = varT (ppVar >>^ \ i -> text "Var" <+> i)
          <+ litT (ppSDoc >>^ \ x -> text "Lit" <+> x)
          <+ appT ppCoreExpr ppCoreExpr (\ a b -> text "App" $$ nest 2 (cat [parens a, parens b]))
          <+ lamT ppVar ppCoreExpr (\ v e -> text "Lam" <+> v $$ nest 2 (parens e))
          <+ letT ppCoreBind ppCoreExpr (\ b e -> text "Let" $$ nest 2 (cat [parens b, parens e]))
          <+ caseT ppCoreExpr ppVar ppType (const ppCoreAlt) (\s w ty alts ->
                    text "Case" $$ nest 2 (parens s) $$ nest 2 w $$ nest 2 (parens ty) $$ nest 2 (vlist alts))
          <+ castT ppCoreExpr ppCoercion (\ e co -> text "Cast" $$ nest 2 (cat [parens e, parens co]))
          <+ tickT ppSDoc ppCoreExpr (\ tk e  -> text "Tick" $$ nest 2 (tk <+> parens e))
          <+ typeT (ppType >>^ \ ty -> text "Type" $$ nest 2 (parens ty))
          <+ coercionT (ppCoercion >>^ \ co -> text "Coercion" $$ nest 2 (parens co))

ppCoreBind :: PrettyH GHC.CoreBind
ppCoreBind = nonRecT ppVar ppCoreExpr (\ v e -> text "NonRec" <+> v $$ nest 2 (parens e))
          <+ recT (const ppCoreDef) (\ bnds -> text "Rec" $$ nest 2 (vlist bnds))

ppCoreAlt :: PrettyH GHC.CoreAlt
ppCoreAlt = altT ppSDoc (\ _ -> ppVar) ppCoreExpr $ \ con vs e -> text "Alt" <+> con <+> hlist vs $$ nest 2 (parens e)

ppCoreDef :: PrettyH CoreDef
ppCoreDef = defT ppVar ppCoreExpr (\ i e -> text "Def" <+> i $$ nest 2 (parens e))

ppType :: PrettyH Type
ppType =  tyVarT (ppVar >>^ \ v -> tyText "TyVarTy" <+> v)
       <+ litTyT (ppSDoc >>^ \ l -> tyText "LitTy" <+> l)
       <+ appTyT ppType ppType (\ ty1 ty2 -> tyText "AppTy" $$ nest 2 (cat [parens ty1, parens ty2]))
       <+ funTyT ppType ppType (\ ty1 ty2 -> tyText "FunTy" $$ nest 2 (cat [parens ty1, parens ty2]))
       <+ forAllTyT ppVar ppType (\ v ty -> tyText "ForAllTy" <+> v $$ nest 2 (parens ty))
       <+ tyConAppT ppSDoc (const ppType) (\ con tys -> tyText "TyConApp" <+> con $$ nest 2 (vlist $ map parens tys))

ppCoercion :: PrettyH Coercion
ppCoercion =  reflT (ppType >>^ \ ty -> coText "Refl" $$ nest 2 (parens ty))
           <+ coVarCoT (ppVar >>^ \ v -> coText "CoVarCo" <+> v)
           <+ symCoT (ppCoercion >>^ \ co -> coText "SymCo" $$ nest 2 (parens co))
           <+ appCoT ppCoercion ppCoercion (\ co1 co2 -> coText "AppCo" $$ nest 2 (cat [parens co1, parens co2]))
           <+ forAllCoT ppVar ppCoercion (\ v co -> coText "ForAllCo" <+> v $$ nest 2 (parens co))
           <+ transCoT ppCoercion ppCoercion (\ co1 co2 -> coText "TransCo" $$ nest 2 (cat [parens co1, parens co2]))
           <+ tyConAppCoT ppSDoc (const ppCoercion) (\ con coes -> coText "TyConAppCo" <+> con $$ nest 2 (vlist $ map parens coes))
           <+ unsafeCoT ppType ppType (\ ty1 ty2 -> coText "UnsafeCo" $$ nest 2 (cat [parens ty1, parens ty2]))
           <+ nthCoT (arr $ coText . show) ppCoercion (\ n co -> coText "NthCo" <+> n $$ parens co)
           <+ instCoT ppCoercion ppType (\ co ty -> coText "InstCo" $$ nest 2 (cat [parens co, parens ty]))
#if __GLASGOW_HASKELL__ > 706
-- TODO: Figure out how to properly pp new branched Axioms and Left/Right Coercions
           <+ axiomInstCoT ppSDoc ppSDoc (const ppCoercion) (\ ax idx coes -> coText "AxiomInstCo" <+> ax <+> idx $$ nest 2 (vlist $ map parens coes))
           <+ lrCoT ppSDoc ppCoercion (\ lr co -> coText "LRCo" <+> lr $$ nest 2 (parens co))
#else
           <+ axiomInstCoT ppSDoc (const ppCoercion) (\ ax coes -> coText "AxiomInstCo" <+> ax $$ nest 2 (vlist $ map parens coes))
#endif

ppVar :: PrettyH Var
ppVar = readerT $ \ v -> ppSDoc >>^ modCol v
  where
    modCol v | GHC.isTyVar v = typeColor
             | GHC.isCoVar v = coercionColor
             | otherwise     = idColor

---------------------------------------------------------------------------
