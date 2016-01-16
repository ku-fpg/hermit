{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}

-- | Output the raw Expr constructors. Helpful for writing pattern matching rewrites.
module HERMIT.PrettyPrinter.AST
  ( -- * HERMIT's AST Pretty-Printer for GHC Core
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
  , ppForallQuantification
  )
where

import Control.Arrow hiding ((<+>))

import Data.Char (isSpace)
import Data.Default.Class

import HERMIT.Core
import HERMIT.External
import HERMIT.GHC hiding (($$), (<+>), (<>), ($+$), cat, nest, parens, text, empty, hsep)
import HERMIT.Kure

import HERMIT.PrettyPrinter.Common

import Text.PrettyPrint.MarkedHughesPJ as PP

---------------------------------------------------------------------------

coText :: String -> DocH
coText = coercionColor . text

tyText :: String -> DocH
tyText = typeColor . text

---------------------------------------------------------------------------

externals :: [External]
externals = [ external "ast" pretty ["AST pretty printer."] ]

pretty :: PrettyPrinter
pretty = PP { pLCoreTC = promoteT ppCoreTC -- TODO
            , pOptions = def
            , pTag = "ast"
            }

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
       <+ promoteTypeT     ppKindOrType
       <+ promoteCoercionT ppCoercion

-- Use for any GHC structure, the 'showSDoc' prefix is to remind us
-- that we are eliding infomation here.
ppSDoc :: Outputable a => PrettyH a
ppSDoc =  do dynFlags   <- constT getDynFlags
             hideNotes  <- (po_notes . prettyC_options) ^<< contextT
             arr (toDoc . (if hideNotes then id else ("showSDoc: " ++)) . showPpr dynFlags)
    where toDoc s | any isSpace s = parens (text s)
                  | otherwise     = text s

ppModGuts :: PrettyH ModGuts
ppModGuts =  mg_module ^>> ppSDoc

ppCoreProg :: PrettyH CoreProg
ppCoreProg = progConsT ppCoreBind ppCoreProg ($+$) <+ progNilT empty

ppCoreExpr :: PrettyH CoreExpr
ppCoreExpr = varT (ppVar >>^ \ i -> text "Var" <+> i)
          <+ litT (ppSDoc >>^ \ x -> text "Lit" <+> x)
          <+ appT ppCoreExpr ppCoreExpr (\ a b -> text "App" $$ nest 2 (cat [parens a, parens b]))
          <+ lamT ppVar ppCoreExpr (\ v e -> text "Lam" <+> v $$ nest 2 (parens e))
          <+ letT ppCoreBind ppCoreExpr (\ b e -> text "Let" $$ nest 2 (cat [parens b, parens e]))
          <+ caseT ppCoreExpr ppVar ppKindOrType (const ppCoreAlt) (\s w ty alts ->
                    text "Case" $$ nest 2 (parens s) $$ nest 2 w $$ nest 2 (parens ty) $$ nest 2 (vlist alts))
          <+ castT ppCoreExpr ppCoercion (\ e co -> text "Cast" $$ nest 2 (cat [parens e, parens co]))
          <+ tickT ppSDoc ppCoreExpr (\ tk e  -> text "Tick" $$ nest 2 (tk <+> parens e))
          <+ typeT (ppKindOrType >>^ \ ty -> text "Type" $$ nest 2 (parens ty))
          <+ coercionT (ppCoercion >>^ \ co -> text "Coercion" $$ nest 2 (parens co))

ppCoreBind :: PrettyH CoreBind
ppCoreBind = nonRecT ppVar ppCoreExpr (\ v e -> text "NonRec" <+> v $$ nest 2 (parens e))
          <+ recT (const ppCoreDef) (\ bnds -> text "Rec" $$ nest 2 (vlist bnds))

ppCoreAlt :: PrettyH CoreAlt
ppCoreAlt = altT ppSDoc (\ _ -> ppVar) ppCoreExpr $ \ con vs e -> text "Alt" <+> con <+> hlist vs $$ nest 2 (parens e)

ppCoreDef :: PrettyH CoreDef
ppCoreDef = defT ppVar ppCoreExpr (\ i e -> text "Def" <+> i $$ nest 2 (parens e))

ppKindOrType :: PrettyH Type
ppKindOrType = readerT $ \case
  TyVarTy{}  -> tyVarT (ppVar >>^ \ v -> tyText "TyVarTy" <+> v)
  AppTy{}    -> appTyT ppKindOrType ppKindOrType (\ ty1 ty2 -> tyText "AppTy" $$ nest 2 (cat [parens ty1, parens ty2]))
  TyConApp{} -> tyConAppT ppSDoc (const ppKindOrType) $ \ con tys -> 
                  tyText "TyConApp" <+> con $$ nest 2 (vlist $ map parens tys)
#if __GLASGOW_HASKELL__ > 710
  CastTy{}   -> castTyT ppKindOrType ppCoercion (\ ty co -> tyText "CastTy" $$ nest 2 (cat [parens ty, parens co]))
  CoercionTy{} -> coercionTyT ppCoercion >>= \ co -> return (tyText "CoercionTy" $$ nest 2 (parens co))
  ForAllTy{} -> forAllTyT ppTyBinder ppKindOrType (\ tb ty -> tyText "ForAllTy" <+> tb $$ nest 2 (parens ty))
#else
  FunTy{}    -> funTyT ppKindOrType ppKindOrType (\ ty1 ty2 -> tyText "FunTy" $$ nest 2 (cat [parens ty1, parens ty2]))
  ForAllTy{} -> forAllTyT ppVar ppKindOrType (\ v ty -> tyText "ForAllTy" <+> v $$ nest 2 (parens ty))
#endif
  LitTy{}    -> litTyT (ppSDoc >>^ \ l -> tyText "LitTy" <+> l)

#if __GLASGOW_HASKELL__ > 710
ppTyBinder :: PrettyH TyBinder
ppTyBinder = readerT $ \case
  Named tv v -> do
    d <- return tv >>> ppVar
    return $ tyText "Named" <+> d <+> tyText (showVis v)
  Anon ty -> do
    d <- return ty >>> ppKindOrType
    return $ tyText "Anon" <+> d

ppUnivCoProvenance :: PrettyH UnivCoProvenance
ppUnivCoProvenance = readerT $ \case
  UnsafeCoerceProv -> return $ coText "UnsafeCoerceProv"
  PhantomProv co -> do
    d <- return co >>> ppCoercion
    return $ coText "PhantomProv" <+> parens d
  ProofIrrelProv co -> do
    d <- return co >>> ppCoercion
    return $ coText "ProofIrrelProv" <+> parens d
  PluginProv s -> return $ coText "PluginProv" <+> coText s
  HoleProv _ -> return $ coText "HoleProv - IMPOSSIBLE!"
#endif

ppCoercion :: PrettyH Coercion
ppCoercion = readerT $ \case
  Refl{}        -> reflT ppKindOrType (\ r ty -> coText "Refl" <+> coText (showRole r) $$ nest 2 (parens ty))
  TyConAppCo{}  -> tyConAppCoT ppSDoc (const ppCoercion) $ \ r con coes -> 
                    coText "TyConAppCo" <+> coText (showRole r) <+> con $$ nest 2 (vlist $ map parens coes)
  AppCo{}       -> appCoT ppCoercion ppCoercion (\ co1 co2 -> coText "AppCo" $$ nest 2 (cat [parens co1, parens co2]))
#if __GLASGOW_HASKELL__ > 710
  ForAllCo{}    -> forAllCoT ppVar ppCoercion ppCoercion $ \ v c1 c2 -> 
                    coText "ForAllCo" <+> v $$ nest 2 (cat [parens c1, parens c2])
#else
  ForAllCo{}    -> forAllCoT ppVar ppCoercion (\ v co -> coText "ForAllCo" <+> v $$ nest 2 (parens co))
#endif
  CoVarCo{}     -> coVarCoT (ppVar >>^ \ v -> coText "CoVarCo" <+> v)
  AxiomInstCo{} -> axiomInstCoT ppSDoc ppSDoc (const ppCoercion) $ \ ax idx coes -> 
                    coText "AxiomInstCo" <+> ax <+> idx $$ nest 2 (vlist $ map parens coes)
#if __GLASGOW_HASKELL__ > 710
  UnivCo p _ _ _ -> do
    pd <- return p >>> ppUnivCoProvenance
    univCoT ppKindOrType ppKindOrType $ \ _ r dom ran -> 
      coText "UnivCo" <+> pd <+> coText (showRole r) $$ nest 2 (cat [parens dom, parens ran])
#else
  UnivCo{}      -> univCoT ppKindOrType ppKindOrType $ \ s r dom ran -> 
                    coText "UnivCo" <+> coText (show s) <+> coText (showRole r) $$ nest 2 (cat [parens dom, parens ran])
#endif
  SymCo{}       -> symCoT (ppCoercion >>^ \ co -> coText "SymCo" $$ nest 2 (parens co))
  TransCo{}     -> transCoT ppCoercion ppCoercion (\ co1 co2 -> coText "TransCo" $$ nest 2 (cat [parens co1, parens co2]))
  NthCo{}       -> nthCoT (arr $ coText . show) ppCoercion (\ n co -> coText "NthCo" <+> n $$ parens co)
  LRCo{}        -> lrCoT ppSDoc ppCoercion (\ lr co -> coText "LRCo" <+> lr $$ nest 2 (parens co))
#if __GLASGOW_HASKELL__ > 710
  InstCo{}      -> instCoT ppCoercion ppCoercion (\ c1 c2 -> coText "InstCo" $$ nest 2 (cat [parens c1, parens c2]))
#else
  InstCo{}      -> instCoT ppCoercion ppKindOrType (\ co ty -> coText "InstCo" $$ nest 2 (cat [parens co, parens ty]))
#endif
  SubCo{}       -> subCoT (ppCoercion >>^ \ co -> coText "SubCo" $$ nest 2 (parens co))

ppVar :: PrettyH Var
ppVar = readerT $ \ v -> ppSDoc >>^ modCol v
  where
    modCol v | isTyVar v  = typeColor
             | isCoVar v  = coercionColor
             | otherwise  = idColor

-- A bit hacky, currently only used to pretty-print Lemmas.
ppForallQuantification :: PrettyH [Var]
ppForallQuantification =
  do vs <- mapT ppVar
     if null vs
     then return empty
     else return $ keywordText "forall" <+> hsep vs <> keywordText "."

keywordText :: String -> DocH
keywordText = keywordColor . text

---------------------------------------------------------------------------
