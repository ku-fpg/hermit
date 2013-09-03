{-# LANGUAGE CPP, LambdaCase, MultiWayIf #-}

module HERMIT.PrettyPrinter.Clean
  ( -- * HERMIT's Clean Pretty-Printer for GHC Core
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
import Control.Applicative ((<$>))

import Data.Char (isSpace)

import HERMIT.Context
import HERMIT.Core
import HERMIT.GHC hiding ((<+>), (<>), ($$), ($+$), sep, hsep, empty, nest, vcat, char, text, keyword, hang)
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Syntax

import HERMIT.Primitive.GHC (dynFlagsT)

import HERMIT.PrettyPrinter.Common

import Pair

import Text.PrettyPrint.MarkedHughesPJ as PP

------------------------------------------------------------------------------------------------

data RetExpr
        = RetLam AbsolutePathH [DocH] AbsolutePathH DocH
        | RetLet AbsolutePathH [DocH] AbsolutePathH DocH
        | RetApp DocH [(AbsolutePathH,RetExpr)]
        | RetForAll AbsolutePathH [DocH] AbsolutePathH DocH
        | RetArrowType DocH [(AbsolutePathH,DocH)] -- f -> (a -> (b -> c))  The path is for each arrow, starting from the left.
        | RetExpr DocH
        | RetAtom DocH         -- parens not needed
        | RetEmpty

retApp :: AbsolutePathH -> Crumb -> Crumb -> RetExpr -> RetExpr -> RetExpr
retApp _ _   _   f              RetEmpty = f
retApp _ _   _   RetEmpty       e        = e
retApp p _   cr2 (RetApp f pes) e        = RetApp f (pes ++ [(p @@ cr2, e)])
retApp p cr1 cr2 f              e        = RetApp (normalParens (p @@ cr1) f) [(p @@ cr2, e)]

-- empties should not arise
retApps :: AbsolutePathH -> (Int -> Crumb) -> DocH -> [RetExpr] -> RetExpr
retApps p crumb f es = RetApp f [ ((p @@ crumb n),e) | (e,n) <- zip es [1..]]

retLam :: AbsolutePathH -> DocH -> RetExpr -> RetExpr
retLam p v = if isEmpty v
              then id
              else \case
                      RetLam _ vs pb e -> RetLam p (v : vs) pb e
                      e                -> RetLam p [v] (p @@ Lam_Body) (normalExpr e)

retLet :: AbsolutePathH -> DocH -> RetExpr -> RetExpr
retLet p bnd = if isEmpty bnd
                then id
                else \case
                        RetLet _ bnds pb body -> RetLet p (bnd : bnds) pb body
                        body                  -> RetLet p [bnd] (p @@ Let_Body) (normalExpr body)

retForAll :: AbsolutePathH -> Crumb -> DocH -> RetExpr -> RetExpr
retForAll p cr v = if isEmpty v
                    then id
                    else \case
                            RetForAll _ vs pb ty  -> RetForAll p (v : vs) pb ty
                            ty                    -> RetForAll p [v] (p @@ cr) (normalExpr ty)

-- This is very hacky.  There must be a better way of handling arrow types.
retArrowType :: AbsolutePathH -> Crumb -> Crumb -> RetExpr -> RetExpr -> RetExpr
retArrowType p cr1 cr2 ty1 = \case
                                RetArrowType ty2 ptys  -> RetArrowType (normalParensExceptApp (p @@ cr1) ty1) ((p,ty2) : ptys)
                                ty2                    -> RetArrowType (normalParensExceptApp (p @@ cr1) ty1) [(p , normalParensExceptApp (p @@ cr2) ty2)]

------------------------------------------------------------------------------------------------

isAtom :: RetExpr -> Bool
isAtom (RetAtom _) = True
isAtom _           = False

------------------------------------------------------------------------------------------------

normalExpr :: RetExpr -> DocH
normalExpr  RetEmpty           = empty
normalExpr (RetAtom e)         = e
normalExpr (RetExpr e)         = e
normalExpr (RetLam p vs pb e)  = hang (specialSymbol p LambdaSymbol <+> hsep vs <+> specialSymbol pb RightArrowSymbol) 2 e
normalExpr (RetLet p vs pb e)  = sep [ keyword p "let" <+> vcat vs, keyword pb "in" <+> e ]
normalExpr (RetApp f pes)      = let (pAtoms,pExprs) = span (isAtom.snd) pes
                                  in sep [ hsep (f : map (normalExpr.snd) pAtoms)
                                         , nest 2 (sep $ map (uncurry normalParens) pExprs) ]
normalExpr (RetForAll p vs pb ty) = specialSymbol p ForallSymbol <+> hsep vs <+> symbol pb '.' <+> ty
normalExpr (RetArrowType ty ptys) = foldl (\ ty1 (p,ty2) -> ty1 <+> typeArrow p <+> ty2) ty ptys

------------------------------------------------------------------------------------------------

cleanParens :: AbsolutePathH -> DocH -> DocH
cleanParens p e = symbol p '(' <> e <> symbol p ')'

normalParens :: AbsolutePathH -> RetExpr -> DocH
normalParens p = \case
                    RetEmpty    -> empty
                    RetAtom e   -> e
                    RetApp f [] -> f
                    e           -> cleanParens p (normalExpr e)

normalParensExceptApp :: AbsolutePathH -> RetExpr -> DocH
normalParensExceptApp p = \case
                             e@RetApp{} -> normalExpr e
                             e          -> normalParens p e

------------------------------------------------------------------------------------------------

parenExpr :: PrettyH RetExpr
parenExpr = do p <- absPathT
               arr (normalParens p)

parenExprExceptApp :: PrettyH RetExpr
parenExprExceptApp = do p <- absPathT
                        arr (normalParensExceptApp p)

------------------------------------------------------------------------------------------------

specialSymbol :: AbsolutePathH -> SpecialSymbol -> DocH
specialSymbol p = attrP p . markColor SyntaxColor . specialFont . char . renderSpecial

symbol :: AbsolutePathH -> Char -> DocH
symbol p = attrP p . markColor SyntaxColor . char

keyword :: AbsolutePathH -> String -> DocH
keyword p = attrP p . markColor KeywordColor . text

idText :: AbsolutePathH -> String -> DocH
idText p = attrP p . text


coText :: AbsolutePathH -> String -> DocH
coText p = attrP p . coercionColor . text

coChar :: AbsolutePathH -> Char -> DocH
coChar p = attrP p . coercionColor . char

coSymbol :: AbsolutePathH -> SpecialSymbol -> DocH
coSymbol p = attrP p . coercionColor . specialFont . char . renderSpecial

castSymbol :: AbsolutePathH -> DocH
castSymbol p = coSymbol p CastSymbol

coercionSymbol :: AbsolutePathH -> DocH
coercionSymbol p = coSymbol p CoercionSymbol

coercionBindSymbol :: AbsolutePathH -> DocH
coercionBindSymbol p = coSymbol p CoercionBindSymbol

coKeyword :: AbsolutePathH -> String -> DocH
coKeyword = coText -- An alternative would be keyword.


tyChar :: AbsolutePathH -> Char -> DocH
tyChar p = attrP p . typeColor . char

tyText :: AbsolutePathH -> String -> DocH
tyText p = attrP p . typeColor . text

tySymbol :: AbsolutePathH -> SpecialSymbol -> DocH
tySymbol p = attrP p . typeColor . specialFont . char . renderSpecial

typeSymbol :: PrettyH a
typeSymbol = do p <- absPathT
                return (tySymbol p TypeSymbol)

typeBindSymbol :: AbsolutePathH -> DocH
typeBindSymbol p = tySymbol p TypeBindSymbol

typeOfSymbol :: AbsolutePathH -> DocH
typeOfSymbol p = tySymbol p TypeOfSymbol

typeArrow :: AbsolutePathH -> DocH
typeArrow p = tySymbol p RightArrowSymbol

------------------------------------------------------------------------------------------------

-- | Pretty print a fragment of GHC Core using HERMIT's \"Clean\" pretty printer.
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


-- Use for any GHC structure
ppSDoc :: Outputable a => PrettyH a
ppSDoc = do dynFlags <- dynFlagsT
            p        <- absPathT
            doc      <- arr (showPpr dynFlags)
            if any isSpace doc
             then return (cleanParens p (idText p doc))
             else return (idText p doc)

ppVar :: PrettyH Var
ppVar = readerT $ \ v -> varName ^>> ppName (varColor v)

varColor :: Var -> SyntaxForColor
varColor var | isTyVar var = TypeColor
             | isCoVar var = CoercionColor
             | otherwise   = IdColor

ppName :: SyntaxForColor -> PrettyH Name
ppName color = do p    <- absPathT
                  name <- arr uqName
                  let doc = attrP p $ markColor color $ text name
                               -- TODO: is "isScriptInfixId" the right predicate to use here?
                  if all isScriptInfixIdChar name
                     then return (cleanParens p doc)
                     else return doc

ppLitTy :: PrettyH TyLit
ppLitTy = do p <- absPathT
             arr $ \ lit -> tyText p $ case lit of
                                         NumTyLit i  -> show i
                                         StrTyLit fs -> show fs

ppTyCon :: PrettyH TyCon
ppTyCon = getName ^>> ppName TypeColor

ppTyConCo :: PrettyH TyCon
ppTyConCo = getName ^>> ppName CoercionColor

-- binders are vars that is bound by lambda or case, etc.
-- depending on the mode, they might not be displayed
ppBinderMode :: PrettyH Var
ppBinderMode = do p    <- absPathT
                  v    <- idR
                  opts <- prettyC_options ^<< contextT
                  if
                     | isTyVar v -> case po_exprTypes opts of
                                                           Omit     -> return empty
                                                           Abstract -> return (typeBindSymbol p)
                                                           _        -> ppVar
                     | isCoVar v -> case po_coercions opts of
                                                           Omit     -> return empty
                                                           Abstract -> return (coercionBindSymbol p)
                                                           Show     -> ppVar
                                                           Kind     -> do pCoKind <- ppCoKind <<^ CoVarCo
                                                                          return $ cleanParens p (coercionBindSymbol p <+> typeOfSymbol p <+> pCoKind)
                                                          -- TODO: refactor this to be more systematic.  It should be possible to request type sigs for all type bindings.
                     | otherwise       -> ppVar

ppModGuts :: PrettyH ModGuts
ppModGuts = do p    <- absPathT
               name <- ppSDoc <<^ mg_module
               modGutsT ppProg (\ _ prog -> hang (keyword p "module" <+> name <+> keyword p "where") 2 prog)
    where
      ppProg :: PrettyH CoreProg
      ppProg = progConsT ppBind ppProg ($+$) <+ progNilT empty

      ppBind :: PrettyH CoreBind
      ppBind =    (absPathT >>= \ p -> nonRecT ppVar (exprKindOrType ^>> ppKindOrType) (\ v ty -> v <+> typeOfSymbol p <+> ty))
               <+ recT (\ _ -> absPathT &&& defT ppVar (exprKindOrType ^>> ppKindOrType) (,)) (\ pvtys -> vcat [ v <+> typeOfSymbol p <+> ty | (p,(v,ty)) <- pvtys ])

ppCoreProg :: PrettyH CoreProg
ppCoreProg = progConsT ppCoreBind ppCoreProg ($+$) <+ progNilT empty

ppCoreBind :: PrettyH CoreBind
ppCoreBind =   (nonRecT idR (ppCoreExprR &&& ppTypeSig) (,) >>> ppDef NonRec_RHS)
            <+ (do p <- absPathT
                   recT (const ppCoreDef) (\ bnds -> keyword p "rec" <+> vcat bnds)
               )


ppCoreAlt :: PrettyH CoreAlt
ppCoreAlt = do p <- absPathT
               altT (do p' <- absPathT
                        readerT $ \case
                                      DataAlt dcon -> return (getName dcon) >>> ppName IdColor
                                      LitAlt lit   -> return lit >>> ppSDoc
                                      DEFAULT      -> return (symbol p' '_')
                    )
                    (\ _ -> ppBinderMode)
                    ppCoreExpr
                    (\ con vs e -> hang (con <+> hsep vs <+> specialSymbol p RightArrowSymbol) 2 e)

ppCoreDef :: PrettyH CoreDef
ppCoreDef = defT idR (ppCoreExprR &&& ppTypeSig) (,) >>> ppDef Def_RHS

ppDef :: Crumb -> PrettyH (Var,(RetExpr,DocH))
ppDef cr = do p          <- absPathT
              (v,(e,ty)) <- idR
              opts       <- prettyC_options ^<< contextT
              let eq = symbol p '='
              case po_coercions opts of
                Omit | isCoVar v  -> return empty
                Kind | isCoVar v  -> return $ case po_exprTypes opts of
                                                    Show -> (coercionBindSymbol p <+> typeOfSymbol p <+> ty) $+$ (coercionBindSymbol p <+> eq <+> coercionSymbol (p @@ cr))
                                                    _    -> coercionBindSymbol p <+> eq <+> normalExpr e
                _                     -> do pv  <- ppBinderMode <<< return v
                                            let pre  = pv <+> eq
                                                body = case e of -- This is an ugly hack
                                                         RetLam p' vs pb e0 -> hang (pre <+> specialSymbol p' LambdaSymbol <+> hsep vs <+> specialSymbol pb RightArrowSymbol) 2 e0
                                                         _                  -> hang pre 2 (normalExpr e)
                                            return $ case po_exprTypes opts of
                                                       Omit | isTyVar v -> empty
                                                       Show                 -> (pv <+> typeOfSymbol p <+> ty) $+$ body
                                                       _                    -> body


ppCoreExpr :: PrettyH CoreExpr
ppCoreExpr = ppCoreExprR >>^ normalExpr

ppCoreExprR :: Translate PrettyC HermitM CoreExpr RetExpr
ppCoreExprR = absPathT >>= ppCoreExprPR
  where
    ppCoreExprPR :: AbsolutePathH -> Translate PrettyC HermitM CoreExpr RetExpr
    ppCoreExprPR p =
              lamT ppBinderMode ppCoreExprR (retLam p)
           <+ letT ppCoreBind ppCoreExprR (retLet p)
           <+ appT ppCoreExprR ppCoreExprR (retApp p App_Fun App_Arg)
           <+ caseT ppCoreExpr ppVar (ppTypeModeR >>> parenExpr) (const ppCoreAlt) (\ s w ty alts -> RetExpr ((keyword p "case" <+> s <+> keyword p "of" <+> w <+> ty) $$ nest 2 (vcat alts)))

           <+ varT (do (c,i) <- exposeT
                       RetAtom <$> if isDeadBinder i ||
                                      (isLocalId i && (i `notElemVarSet` boundVars c))
                                    then varName ^>> ppName WarningColor
                                    else ppVar
                   )

           <+ litT (RetAtom <$> ppSDoc)
           <+ typeT ppTypeModeR
           <+ coercionT ppCoercionModeR
           <+ (castT ppCoreExprR (ppCoercionModeR >>> parenExpr) (,) >>> readerT (\ (_,co) -> if isEmpty co
                                                                                                 then arr fst
                                                                                                 else toFst parenExprExceptApp >>^ \ e -> RetExpr (e <+> castSymbol p <+> co)
                                                                                 ))
           <+ tickT ppSDoc (ppCoreExprR >>> parenExpr) (\ tk e -> RetExpr $ attrP p (text "Tick") $$ nest 2 (tk <+> e))

--------------------------------------------------------------------

ppKindOrType :: PrettyH KindOrType
ppKindOrType = ppKindOrTypeR >>^ normalExpr

ppTypeModeR :: Translate PrettyC HermitM KindOrType RetExpr
ppTypeModeR =
  do opts <- prettyC_options ^<< contextT
     case po_exprTypes opts of
       Omit     -> return RetEmpty
       Abstract -> RetAtom <$> typeSymbol
       _        -> ppKindOrTypeR

ppKindOrTypeR :: Translate PrettyC HermitM KindOrType RetExpr
ppKindOrTypeR = absPathT >>= ppKindOrTypePR
  where
    ppKindOrTypePR :: AbsolutePathH -> Translate PrettyC HermitM KindOrType RetExpr
    ppKindOrTypePR p =
           tyVarT (RetAtom <$> ppVar)
        <+ litTyT (RetAtom <$> ppLitTy)
        <+ appTyT ppKindOrTypeR ppKindOrTypeR (retApp p AppTy_Fun AppTy_Arg)
        <+ funTyT ppKindOrTypeR ppKindOrTypeR (retArrowType p FunTy_Dom FunTy_CoDom)
        <+ forAllTyT ppVar ppKindOrTypeR (retForAll p ForAllTy_Body)
        <+ tyConAppT (forkFirst ppTyCon) (\ _ -> ppKindOrTypeR)
             (\ (pCon,tyCon) tys -> if | isFunTyCon tyCon && length tys == 2 -> let [ty1,ty2] = tys in retArrowType p (TyConApp_Arg 0) (TyConApp_Arg 1) ty1 ty2
                                       | tyCon == listTyCon -> RetAtom $ tyChar p '[' <> (case tys of
                                                                                                []  -> empty
                                                                                                t:_ -> normalExpr t)
                                                                                          <> tyChar p ']'
                                       | isTupleTyCon tyCon -> RetAtom $ tyChar p '(' <> (if null tys
                                                                                               then empty
                                                                                               else foldr1 (\ ty r -> ty <> tyChar p ',' <+> r) (map normalExpr tys)
                                                                                             )
                                                                                          <> tyChar p ')'
                                       | isLiftedTypeKindCon tyCon -> RetAtom $ tyChar p '*'
                                       | otherwise                 -> retApps p TyConApp_Arg pCon tys
             )

--------------------------------------------------------------------

ppCoercion :: PrettyH Coercion
ppCoercion = ppCoercionR >>^ normalExpr

ppCoercionModeR :: Translate PrettyC HermitM Coercion RetExpr
ppCoercionModeR = do p    <- absPathT
                     opts <- prettyC_options ^<< contextT
                     case po_coercions opts of
                       Omit     -> return RetEmpty
                       Abstract -> return (RetAtom $ coercionSymbol p)
                       Show     -> ppCoercionR
                       Kind     -> ppCoKind >>^ (\ k -> RetExpr (coercionSymbol p <+> typeOfSymbol p <+> k))

ppCoercionR :: Translate PrettyC HermitM Coercion RetExpr
ppCoercionR = absPathT >>= ppCoercionPR
  where
    ppCoercionPR :: AbsolutePathH -> Translate PrettyC HermitM Coercion RetExpr
    ppCoercionPR p =
                   reflT (ppTypeModeR >>^ normalExpr >>^ \ ty -> RetAtom $ if isEmpty ty then coText p "refl" else coChar p '<' <> ty <> coChar p '>')
                <+ coVarCoT (RetAtom <$> ppVar)
                <+ symCoT (ppCoercionR >>> parenExpr >>^ \ co -> RetExpr (coKeyword p "sym" <+> co))
                <+ forAllCoT ppBinderMode ppCoercionR (retForAll p ForAllCo_Body)
                <+ transCoT (ppCoercionR >>> parenExprExceptApp) (ppCoercionR >>> parenExprExceptApp) (\ co1 co2 -> RetExpr (co1 <+> coChar p ';' <+> co2))
                <+ unsafeCoT (ppTypeModeR >>> parenExpr) (ppTypeModeR >>> parenExpr) (\ ty1 ty2 -> (if isEmpty ty1 && isEmpty ty2 then RetAtom else RetExpr)
                                                                                                   (coKeyword p "unsafe" <+> ty1 <+> ty2)
                                                     )
                <+ nthCoT (arr show) (ppCoercionR >>> parenExpr) (\ n co -> RetExpr (coKeyword p "nth" <+> coText (p @@ NthCo_Int) n <+> co))
                <+ instCoT (ppCoercionR >>> parenExpr &&& parenExprExceptApp) (ppTypeModeR >>> parenExprExceptApp) (\ (cop1,cop2) ty -> if isEmpty ty
                                                                                                                                         then RetExpr (coText p "inst" <+> cop1)
                                                                                                                                         else RetExpr (cop2 <+> coChar p '@' <+> ty)
                                                                                                                   )
                <+ tyConAppCoT ppTyConCo (const ppCoercionR) (retApps p TyConApp_Arg)
                <+ appCoT ppCoercionR ppCoercionR (retApp p AppCo_Fun AppCo_Arg)
#if __GLASGOW_HASKELL__ > 706
-- TODO: Figure out how to properly pp new branched Axioms and Left/Right Coercions
                <+ axiomInstCoT (coAxiomName ^>> ppName CoercionColor) ppSDoc (\ _ -> ppCoercionR >>> parenExpr) (\ ax idx coes -> RetExpr (coText p "axiomInst" <+> ax <+> idx <+> sep coes))
                <+ lrCoT ppSDoc (ppCoercionR >>> parenExpr) (\ lr co -> RetExpr (coercionColor lr <+> co))
#else
                <+ axiomInstCoT (coAxiomName ^>> ppName CoercionColor) (\ _ -> ppCoercionR >>> parenExpr) (\ ax coes -> RetExpr (coText p "axiomInst" <+> ax <+> sep coes))
#endif

ppCoKind :: PrettyH Coercion
ppCoKind = do p <- absPathT
              (coercionKind >>> unPair) ^>> ((ppTypeModeR >>> parenExprExceptApp) *** (ppTypeModeR >>> parenExprExceptApp)) >>^ ( \(ty1,ty2) -> ty1 <+> coText p "~#" <+> ty2)

--------------------------------------------------------------------

ppTypeSig :: PrettyH CoreExpr
ppTypeSig = coercionT ppCoKind <+ (exprKindOrType ^>> ppKindOrType)

------------------------------------------------------------------------------------------------
