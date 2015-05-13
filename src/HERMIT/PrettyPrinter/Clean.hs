{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NoImplicitPrelude #-}

module HERMIT.PrettyPrinter.Clean
    ( -- * HERMIT's Clean Pretty-Printer for GHC Core
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
    , symbol -- should be in Common
    ) where

import Control.Arrow hiding ((<+>))

import Data.Char (isSpace)
import Data.Default.Class

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC hiding ((<+>), (<>), ($$), ($+$), cat, sep, fsep, hsep, empty, nest, vcat, char, text, keyword, hang)
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.PrettyPrinter.Common
import HERMIT.Syntax

import Prelude.Compat hiding ((<$>))

import Text.PrettyPrint.MarkedHughesPJ as PP

------------------------------------------------------------------------------------------------

externals :: [External]
externals = [ external "clean" pretty ["Clean pretty printer."] ]

pretty :: PrettyPrinter
pretty = PP { pForall = ppForallQuantification
            , pCoreTC = ppCoreTC
            , pOptions = def
            }

data RetExpr
        = RetLam AbsolutePathH [DocH] AbsolutePathH DocH
        | RetLet AbsolutePathH [DocH] AbsolutePathH DocH
        | RetApp DocH [(AbsolutePathH,RetExpr)]
        | RetForAll AbsolutePathH [DocH] AbsolutePathH DocH
        | RetArrowType ArrowType DocH [(AbsolutePathH,DocH)] -- f -> (a -> (b -> c))  The path is for each arrow, starting from the left.
        | RetExpr DocH
        | RetAtom DocH         -- parens not needed
        | RetEmpty

data ArrowType = ATType | ATCoercion deriving (Eq, Show)

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
retArrowType :: ArrowType -> AbsolutePathH -> Crumb -> Crumb -> RetExpr -> RetExpr -> RetExpr
retArrowType at@ATType p cr1 _cr2 ty1 (RetArrowType _ ty2 ptys)
    = RetArrowType at (normalParensExceptApp (p @@ cr1) ty1) ((p,ty2) : ptys)
retArrowType at        p cr1 cr2  ty1 ty2
    = RetArrowType at (normalParensExceptApp (p @@ cr1) ty1) [(p , normalParensExceptApp (p @@ cr2) ty2)]

------------------------------------------------------------------------------------------------

normalExpr :: RetExpr -> DocH
normalExpr  RetEmpty           = empty
normalExpr (RetAtom e)         = e
normalExpr (RetExpr e)         = e
normalExpr (RetLam p vs pb e)  = hang (specialSymbol p LambdaSymbol <+> hsep vs <+> specialSymbol pb RightArrowSymbol) 2 e
normalExpr (RetLet p vs pb e)  = sep [ keyword p "let" <+> vcat vs, keyword pb "in" <+> e ]
normalExpr (RetApp f pes)      = f <+> fsep (map (uncurry normalParens) pes)
normalExpr (RetForAll p vs pb ty) = specialSymbol p ForallSymbol <+> hsep vs <+> symbol pb '.' <+> ty
normalExpr (RetArrowType at ty ptys) = let a = case at of
                                                ATType -> typeArrow
                                                ATCoercion -> coArrow
                                       in foldl (\ ty1 (p,ty2) -> ty1 <+> a p <+> ty2) ty ptys

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

coArrow :: AbsolutePathH -> DocH
coArrow p = coSymbol p RightArrowSymbol

coTypeSymbol :: AbsolutePathH -> DocH
coTypeSymbol p = coSymbol p TypeOfSymbol

------------------------------------------------------------------------------------------------

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
ppSDoc = do dynFlags <- constT getDynFlags
            p        <- absPathT
            doc      <- arr (showPpr dynFlags)
            if any isSpace doc
             then return (cleanParens p (idText p doc))
             else return (idText p doc)

-- For var bindings
ppVar :: PrettyH Var
ppVar = readerT $ \ v -> varName ^>> ppName (varColor v)

-- For var occurences (in CoreExpr)
ppVarOcc :: PrettyH Var
ppVarOcc = do
    (c,i) <- exposeT
    let colFn = if isDeadBinder i || (isLocalId i && (i `notElemVarSet` boundVars c))
                then const WarningColor
                else varColor
    markBindingSite i c <$> (readerT $ \ v -> varName ^>> ppName (colFn v))

varColor :: Var -> SyntaxForColor
varColor var | isTyVar var = TypeColor
             | isCoVar var = CoercionColor
             | otherwise   = IdColor

ppName :: SyntaxForColor -> PrettyH Name
ppName color = do p    <- absPathT
                  c    <- contextT
                  name <- arr (\ n -> unqualifiedName n ++ (if po_showUniques (prettyC_options c)
                                                            then '_' : show (getUnique n) else ""))
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

ppDetailedVar :: PrettyH Var
ppDetailedVar = do
    p <- absPathT
    (v,ty) <- ppVar &&& (varType ^>> ppKindOrType)
    return $ cleanParens p $ v <+> typeOfSymbol p <+> ty

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
                                                           Detailed -> ppDetailedVar
                                                           _        -> ppVar
                     | isCoVar v -> case po_coercions opts of
                                                           Omit     -> return empty
                                                           Abstract -> return (coercionBindSymbol p)
                                                           Detailed -> ppDetailedVar
                                                           Show     -> ppVar
                                                           Kind     -> do pCoKind <- ppCoKind <<^ CoVarCo
                                                                          return $ cleanParens p (coercionBindSymbol p <+> typeOfSymbol p <+> pCoKind)
                                                          -- TODO: refactor this to be more systematic.  It should be possible to request type sigs for all type bindings.
                     | otherwise -> case po_exprTypes opts of
                                        Detailed -> ppDetailedVar
                                        _        -> ppVar

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
                    (\ con vs e -> hang (con <+> fsep vs <+> specialSymbol p RightArrowSymbol) 2 e)

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

ppCoreExprR :: Transform PrettyC HermitM CoreExpr RetExpr
ppCoreExprR = absPathT >>= ppCoreExprPR
  where
    ppCoreExprPR :: AbsolutePathH -> Transform PrettyC HermitM CoreExpr RetExpr
    ppCoreExprPR p =
              lamT ppBinderMode ppCoreExprR (retLam p)
           <+ letT ppCoreBind ppCoreExprR (retLet p)
           <+ appT ppCoreExprR ppCoreExprR (retApp p App_Fun App_Arg)
           <+ caseT ppCoreExpr ppVar (ppTypeModeR >>> parenExpr) (const ppCoreAlt)
                (\ s w ty alts -> RetExpr (hang (keyword p "case" <+> s) 1 (keyword p "of" <+> w <+> ty) $+$ nest 2 (vcat alts)))
           <+ varT (RetAtom <$> ppVarOcc)
           <+ litT (RetAtom <$> ppSDoc)
           <+ typeT ppTypeModeR
           <+ coercionT ppCoercionModeR
           <+ (castT ppCoreExprR (ppCoercionModeR >>> parenExpr) (,) >>> readerT (\ (_,co) -> if isEmpty co
                                                                                                 then arr fst
                                                                                                 else toFst parenExprExceptApp >>^ \ e -> RetExpr (hang e 2 (castSymbol p <+> co))
                                                                                 ))
           <+ tickT ppSDoc (ppCoreExprR >>> parenExpr) (\ tk e -> RetExpr $ attrP p (text "Tick") $$ nest 2 (tk <+> e))

--------------------------------------------------------------------

ppKindOrType :: PrettyH KindOrType
ppKindOrType = ppKindOrTypeR >>^ normalExpr

ppTypeModeR :: Transform PrettyC HermitM KindOrType RetExpr
ppTypeModeR =
  do opts <- prettyC_options ^<< contextT
     case po_exprTypes opts of
       Omit     -> return RetEmpty
       Abstract -> RetAtom <$> typeSymbol
       _        -> ppKindOrTypeR

ppKindOrTypeR :: Transform PrettyC HermitM KindOrType RetExpr
ppKindOrTypeR = absPathT >>= ppKindOrTypePR
  where
    ppKindOrTypePR :: AbsolutePathH -> Transform PrettyC HermitM KindOrType RetExpr
    ppKindOrTypePR p =
           tyVarT (RetAtom <$> ppVarOcc)
        <+ litTyT (RetAtom <$> ppLitTy)
        <+ appTyT ppKindOrTypeR ppKindOrTypeR (retApp p AppTy_Fun AppTy_Arg)
        <+ funTyT ppKindOrTypeR ppKindOrTypeR (retArrowType ATType p FunTy_Dom FunTy_CoDom)
        <+ forAllTyT ppVar ppKindOrTypeR (retForAll p ForAllTy_Body)
        <+ tyConAppT (forkFirst ppTyCon) (\ _ -> ppKindOrTypeR)
             (\ (pCon,tyCon) tys -> if | isFunTyCon tyCon && length tys == 2 -> let [ty1,ty2] = tys in retArrowType ATType p (TyConApp_Arg 0) (TyConApp_Arg 1) ty1 ty2
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


-- A bit hacky, currently only used to pretty-print Lemmas.
ppForallQuantification :: PrettyH [Var]
ppForallQuantification =
  do vs <- mapT ppBinderMode
     if null $ filter (not . isEmpty) vs
     then return empty
     else return $ specialSymbol mempty ForallSymbol <+> sep vs <> symbol mempty '.'

--------------------------------------------------------------------

ppCoercion :: PrettyH Coercion
ppCoercion = ppCoercionR >>^ normalExpr

ppCoercionModeR :: Transform PrettyC HermitM Coercion RetExpr
ppCoercionModeR = do p    <- absPathT
                     opts <- prettyC_options ^<< contextT
                     case po_coercions opts of
                       Omit     -> return RetEmpty
                       Abstract -> return (RetAtom $ coercionSymbol p)
                       Kind     -> ppCoKind >>^ (\ k -> RetExpr (coercionSymbol p <+> coTypeSymbol p <+> k))
                       _        -> ppCoercionR

ppCoercionR :: Transform PrettyC HermitM Coercion RetExpr
ppCoercionR = absPathT >>= ppCoercionPR
  where
    ppCoercionPR :: AbsolutePathH -> Transform PrettyC HermitM Coercion RetExpr
    ppCoercionPR p =
                   coVarCoT (RetAtom <$> ppVarOcc)
                <+ symCoT (ppCoercionR >>> parenExpr >>^ \ co -> RetExpr (coKeyword p "sym" <+> co))
                <+ forAllCoT ppBinderMode ppCoercionR (retForAll p ForAllCo_Body)
                <+ transCoT (ppCoercionR >>> parenExprExceptApp) (ppCoercionR >>> parenExprExceptApp) (\ co1 co2 -> RetExpr (co1 <+> coChar p ';' <+> co2))
                <+ nthCoT (arr show) (ppCoercionR >>> parenExpr) (\ n co -> RetExpr (coKeyword p "nth" <+> coText (p @@ NthCo_Int) n <+> co))
                <+ instCoT (ppCoercionR >>> parenExpr &&& parenExprExceptApp) (ppTypeModeR >>> parenExprExceptApp) (\ (cop1,cop2) ty -> if isEmpty ty
                                                                                                                                         then RetExpr (coText p "inst" <+> cop1)
                                                                                                                                         else RetExpr (cop2 <+> coChar p '@' <+> ty)
                                                                                                                   )
                <+ appCoT ppCoercionR ppCoercionR (retApp p AppCo_Fun AppCo_Arg)
-- TODO: Figure out how to properly pp new branched Axioms and Left/Right Coercions
                <+ reflT (ppTypeModeR >>^ normalExpr) (\ r ty -> RetAtom $ if isEmpty ty then coText p "refl" else coChar p '<' <> coText p (showRole r ++ ":") <> ty <> coChar p '>')
                <+ tyConAppCoT (forkFirst ppTyConCo) (const ppCoercionR)
                               (\ r (ptc, tc) cs -> if isFunTyCon tc && (length cs == 2)
                                                    then let [c1,c2] = cs
                                                         in retArrowType ATCoercion p (TyConApp_Arg 0) (TyConApp_Arg 1) c1 c2
                                                    else retApps p TyConApp_Arg (coText p (showRole r ++ ":") <> ptc) cs)
                <+ axiomInstCoT (coAxiomName ^>> ppName CoercionColor) ppSDoc (\ _ -> ppCoercionR >>> parenExpr) (\ ax idx coes -> RetExpr (coText p "axiomInst" <+> ax <+> idx <+> sep coes))
                <+ lrCoT ppSDoc (ppCoercionR >>> parenExpr) (\ lr co -> RetExpr (coercionColor lr <+> co))
                -- TODO: UnivCo and SubCo
                <+ constT (return . RetAtom $ text "Unsupported Coercion Constructor")

ppCoKind :: PrettyH Coercion
ppCoKind = do
    p <- absPathT
    (r, Pair co1 co2) <- arr (coercionRole &&& coercionKind)
    ty1 <- return co1 >>> ppTypeModeR >>> parenExprExceptApp
    ty2 <- return co2 >>> ppTypeModeR >>> parenExprExceptApp
    return $ cat [ty1, pad (coText p ("~" ++ showRole r)), ty2]

--------------------------------------------------------------------

ppTypeSig :: PrettyH CoreExpr
ppTypeSig = coercionT ppCoKind <+ (exprKindOrType ^>> ppKindOrType)

------------------------------------------------------------------------------------------------
