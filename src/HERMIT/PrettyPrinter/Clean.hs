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
    ) where

import Control.Arrow hiding ((<+>))

import Data.Char (isSpace)
import Data.Default.Class

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC hiding ((<+>), (<>), ($$), ($+$), cat, sep, fsep, hsep, empty, nest, vcat, char, text, keyword, hang)
import HERMIT.Kure hiding ((<$>))
import HERMIT.Lemma
import HERMIT.Monad
import HERMIT.PrettyPrinter.Common
import HERMIT.Syntax

import Prelude.Compat

import Text.PrettyPrint.MarkedHughesPJ as PP

------------------------------------------------------------------------------------------------

externals :: [External]
externals = [ external "clean" pretty ["Clean pretty printer."] ]

pretty :: PrettyPrinter
pretty = PP { pLCoreTC = promoteT ppClauseT <+ promoteT ppCoreTC
            , pOptions = def
            , pTag = "clean"
            }

data RetExpr
        = RetLam [DocH] DocH
        | RetLet [DocH] DocH
        | RetApp DocH [RetExpr]
        | RetForAll [DocH] DocH
        | RetArrowType ArrowType DocH [DocH]
        | RetExpr DocH
        | RetAtom DocH         -- parens not needed
        | RetEmpty

data ArrowType = ATType | ATCoercion deriving (Eq, Show)

retApp :: RetExpr -> RetExpr -> RetExpr
retApp f              RetEmpty = f
retApp RetEmpty       e        = e
retApp (RetApp f es)  e        = RetApp f (es ++ [e])
retApp f              e        = RetApp (normalParens f) [e]

-- empties should not arise
retApps :: DocH -> [RetExpr] -> RetExpr
retApps = RetApp

retLam :: DocH -> RetExpr -> RetExpr
retLam v = if isEmpty v
           then id
           else \case
                   RetLam vs e -> RetLam (v : vs) e
                   e           -> RetLam [v] (normalExpr e)

retLet :: DocH -> RetExpr -> RetExpr
retLet bnd = if isEmpty bnd
             then id
             else \case
                     RetLet bnds body -> RetLet (bnd : bnds) body
                     body             -> RetLet [bnd] (normalExpr body)

retForAll :: DocH -> RetExpr -> RetExpr
retForAll v = if isEmpty v
              then id
              else \case
                      RetForAll vs ty  -> RetForAll (v : vs) ty
                      ty               -> RetForAll [v] (normalExpr ty)

-- This is very hacky.  There must be a better way of handling arrow types.
retArrowType :: ArrowType -> RetExpr -> RetExpr -> RetExpr
retArrowType at@ATType ty1 (RetArrowType _ ty2 tys)
    = RetArrowType at (normalParensExceptApp ty1) (ty2 : tys)
retArrowType at        ty1 ty2
    = RetArrowType at (normalParensExceptApp ty1) [normalParensExceptApp ty2]

------------------------------------------------------------------------------------------------

normalExpr :: RetExpr -> DocH
normalExpr  RetEmpty           = empty
normalExpr (RetAtom e)         = e
normalExpr (RetExpr e)         = e
normalExpr (RetLam vs e)  = hang (specialSymbol LambdaSymbol <+> hsep vs <+> specialSymbol RightArrowSymbol) 2 e
normalExpr (RetLet vs e)  = sep [ keyword "let" <+> vcat vs, keyword "in" <+> e ]
normalExpr (RetApp f es)      = f <+> fsep (map normalParens es)
normalExpr (RetForAll vs ty) = specialSymbol ForallSymbol <+> hsep vs <+> symbol '.' <+> ty
normalExpr (RetArrowType at ty tys) = let a = case at of
                                                ATType -> typeArrow
                                                ATCoercion -> coArrow
                                       in foldl (\ ty1 ty2 -> ty1 <+> a <+> ty2) ty tys

------------------------------------------------------------------------------------------------

cleanParens :: DocH -> DocH
cleanParens e = symbol '(' <> e <> symbol ')'

normalParens :: RetExpr -> DocH
normalParens = \case
                  RetEmpty    -> empty
                  RetAtom e   -> e
                  RetApp f [] -> f
                  e           -> cleanParens (normalExpr e)

normalParensExceptApp :: RetExpr -> DocH
normalParensExceptApp = \case
                           e@RetApp{} -> normalExpr e
                           e          -> normalParens e

------------------------------------------------------------------------------------------------

parenExpr :: PrettyH RetExpr
parenExpr = arr normalParens

parenExprExceptApp :: PrettyH RetExpr
parenExprExceptApp = arr normalParensExceptApp

------------------------------------------------------------------------------------------------

coText :: String -> DocH
coText = coercionColor . text

coChar :: Char -> DocH
coChar = coercionColor . char

coSymbol :: SpecialSymbol -> DocH
coSymbol = coercionColor . specialFont . char . renderSpecial

castSymbol :: DocH
castSymbol = coSymbol CastSymbol

coercionSymbol :: DocH
coercionSymbol = coSymbol CoercionSymbol

coercionBindSymbol :: DocH
coercionBindSymbol = coSymbol CoercionBindSymbol

coKeyword :: String -> DocH
coKeyword = coText -- An alternative would be keyword.

coArrow :: DocH
coArrow = coSymbol RightArrowSymbol

coTypeSymbol :: DocH
coTypeSymbol = coSymbol TypeOfSymbol

------------------------------------------------------------------------------------------------

tyChar :: Char -> DocH
tyChar = typeColor . char

tyText :: String -> DocH
tyText = typeColor . text

tySymbol :: SpecialSymbol -> DocH
tySymbol = typeColor . specialFont . char . renderSpecial

typeSymbol :: PrettyH a
typeSymbol = return (tySymbol TypeSymbol)

typeBindSymbol :: DocH
typeBindSymbol = tySymbol TypeBindSymbol

typeOfSymbol :: DocH
typeOfSymbol = tySymbol TypeOfSymbol

typeArrow :: DocH
typeArrow = tySymbol RightArrowSymbol

------------------------------------------------------------------------------------------------

ppForallT :: PrettyH [Var]
ppForallT = do
    vs <- mapT ppBinderMode
    if null $ filter (not . isEmpty) vs
    then return empty
    else return $ specialSymbol ForallSymbol <+> sep vs <> symbol '.'

ppClauseT :: PrettyH Clause
ppClauseT =
    let parenify = ppClauseT >>^ \ d -> syntaxColor (PP.text "(") PP.<> d PP.<> syntaxColor (PP.text ")")
    in (forallsT ppForallT ppClauseT (\ d1 d2 -> PP.sep [d1,d2])
        <+ conjT parenify parenify (\ d1 d2 -> PP.sep [d1,syntaxColor (specialSymbol ConjSymbol),d2])
        <+ disjT parenify parenify (\ d1 d2 -> PP.sep [d1,syntaxColor (specialSymbol DisjSymbol),d2])
        <+ implT parenify parenify (\ _nm d1 d2 -> PP.sep [d1,syntaxColor (specialSymbol ImplSymbol),d2])
        <+ equivT (extractT ppCoreTC) (extractT ppCoreTC) (\ d1 d2 -> PP.sep [d1,specialSymbol EquivSymbol,d2])
        <+ return (syntaxColor $ PP.text "true"))

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
            doc      <- arr (showPpr dynFlags)
            if any isSpace doc
             then return (cleanParens (text doc))
             else return (text doc)

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
    readerT $ \ v -> varName ^>> ppName (colFn v)

varColor :: Var -> SyntaxForColor
varColor var | isTyVar var = TypeColor
             | isCoVar var = CoercionColor
             | otherwise   = IdColor

ppName :: SyntaxForColor -> PrettyH Name
ppName color = do c    <- contextT
                  name <- arr (\ n -> unqualifiedName n ++ (if po_showUniques (prettyC_options c)
                                                            then '_' : show (getUnique n) else ""))
                  let doc = markColor color $ text name
                               -- TODO: is "isScriptInfixId" the right predicate to use here?
                  if all isScriptInfixIdChar name
                     then return (cleanParens doc)
                     else return doc

ppLitTy :: PrettyH TyLit
ppLitTy = arr $ \ lit -> tyText $ case lit of
                                    NumTyLit i  -> show i
                                    StrTyLit fs -> show fs

ppTyCon :: PrettyH TyCon
ppTyCon = getName ^>> ppName TypeColor

ppTyConCo :: PrettyH TyCon
ppTyConCo = getName ^>> ppName CoercionColor

ppDetailedVar :: PrettyH Var
ppDetailedVar = do
    (v,ty) <- ppVar &&& (varType ^>> ppKindOrType)
    return $ cleanParens $ v <+> typeOfSymbol <+> ty

-- binders are vars that is bound by lambda or case, etc.
-- depending on the mode, they might not be displayed
ppBinderMode :: PrettyH Var
ppBinderMode = do
    v    <- idR
    opts <- prettyC_options ^<< contextT
    if | isTyVar v -> case po_exprTypes opts of
                        Omit     -> return empty
                        Abstract -> return typeBindSymbol
                        Detailed -> ppDetailedVar
                        _        -> ppVar
       | isCoVar v -> case po_coercions opts of
                        Omit     -> return empty
                        Abstract -> return coercionBindSymbol
                        Detailed -> ppDetailedVar
                        Show     -> ppVar
                        Kind     -> do pCoKind <- ppCoKind <<^ CoVarCo
                                       return $ cleanParens (coercionBindSymbol <+> typeOfSymbol <+> pCoKind)
                                       -- TODO: refactor this to be more systematic.
                                       -- It should be possible to request type sigs for all type bindings.
       | otherwise -> case po_exprTypes opts of
                        Detailed -> ppDetailedVar
                        _        -> ppVar

ppModGuts :: PrettyH ModGuts
ppModGuts = do name <- ppSDoc <<^ mg_module
               modGutsT ppProg (\ _ prog -> hang (keyword "module" <+> name <+> keyword "where") 2 prog)
    where
      ppProg :: PrettyH CoreProg
      ppProg = progConsT ppBind ppProg ($+$) <+ progNilT empty

      ppBind :: PrettyH CoreBind
      ppBind =    (nonRecT ppVar (exprKindOrType ^>> ppKindOrType) (\ v ty -> v <+> typeOfSymbol <+> ty))
               <+ recT (\ _ -> defT ppVar (exprKindOrType ^>> ppKindOrType) (,)) (\ pvtys -> vcat [ v <+> typeOfSymbol <+> ty | (v,ty) <- pvtys ])

ppCoreProg :: PrettyH CoreProg
ppCoreProg = progConsT ppCoreBind ppCoreProg ($+$) <+ progNilT empty

ppCoreBind :: PrettyH CoreBind
ppCoreBind =   (nonRecT idR (ppCoreExprR &&& ppTypeSig) (,) >>> ppDef)
            <+ (recT (const ppCoreDef) (\ bnds -> keyword "rec" <+> vcat bnds)
               )


ppCoreAlt :: PrettyH CoreAlt
ppCoreAlt = altT (do readerT $ \case
                             DataAlt dcon -> return (getName dcon) >>> ppName IdColor
                             LitAlt lit   -> return lit >>> ppSDoc
                             DEFAULT      -> return (symbol '_')
                 )
            (\ _ -> ppBinderMode)
            ppCoreExpr
            (\ con vs e -> hang (con <+> fsep vs <+> specialSymbol RightArrowSymbol) 2 e)

ppCoreDef :: PrettyH CoreDef
ppCoreDef = defT idR (ppCoreExprR &&& ppTypeSig) (,) >>> ppDef

ppDef :: PrettyH (Var,(RetExpr,DocH))
ppDef = do (v,(e,ty)) <- idR
           opts       <- prettyC_options ^<< contextT
           let eq = symbol '='
           case po_coercions opts of
             Omit | isCoVar v  -> return empty
             Kind | isCoVar v  -> return $ case po_exprTypes opts of
                                                 Show -> (coercionBindSymbol <+> typeOfSymbol <+> ty) $+$ (coercionBindSymbol <+> eq <+> coercionSymbol)
                                                 _    -> coercionBindSymbol <+> eq <+> normalExpr e
             _                     -> do pv  <- ppBinderMode <<< return v
                                         let pre  = pv <+> eq
                                             body = case e of -- This is an ugly hack
                                                      RetLam vs e0 -> hang (pre <+> specialSymbol LambdaSymbol <+> hsep vs <+> specialSymbol RightArrowSymbol) 2 e0
                                                      _                  -> hang pre 2 (normalExpr e)
                                         return $ case po_exprTypes opts of
                                                    Omit | isTyVar v -> empty
                                                    Show                 -> (pv <+> typeOfSymbol <+> ty) $+$ body
                                                    _                    -> body


ppCoreExpr :: PrettyH CoreExpr
ppCoreExpr = ppCoreExprR >>^ normalExpr

ppCoreExprR :: Transform PrettyC HermitM CoreExpr RetExpr
ppCoreExprR =
    lamT ppBinderMode ppCoreExprR retLam
 <+ letT ppCoreBind ppCoreExprR retLet
 <+ appT ppCoreExprR ppCoreExprR retApp
 <+ caseT ppCoreExpr ppVar (ppTypeModeR >>> parenExpr) (const ppCoreAlt)
                           (\ s w ty alts -> RetExpr (hang (keyword "case" <+> s) 1 (keyword "of" <+> w <+> ty) $+$ nest 2 (vcat alts)))
 <+ varT (RetAtom <$> ppVarOcc)
 <+ litT (RetAtom <$> ppSDoc)
 <+ typeT ppTypeModeR
 <+ coercionT ppCoercionModeR
 <+ (castT ppCoreExprR (ppCoercionModeR >>> parenExpr) (,) >>> readerT (\ (_,co) -> if isEmpty co
                                                                                    then arr fst
                                                                                    else toFst parenExprExceptApp >>^ \ e -> RetExpr (hang e 2 (castSymbol <+> co))
                                                                                 ))
 <+ tickT ppSDoc (ppCoreExprR >>> parenExpr) (\ tk e -> RetExpr $ (text "Tick") $$ nest 2 (tk <+> e))

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
ppKindOrTypeR =
    tyVarT (RetAtom <$> ppVarOcc)
 <+ litTyT (RetAtom <$> ppLitTy)
 <+ appTyT ppKindOrTypeR ppKindOrTypeR retApp
 <+ funTyT ppKindOrTypeR ppKindOrTypeR (retArrowType ATType)
 <+ forAllTyT ppVar ppKindOrTypeR retForAll
 <+ tyConAppT (forkFirst ppTyCon) (\ _ -> ppKindOrTypeR)
              (\ (pCon,tyCon) tys -> if | isFunTyCon tyCon && length tys == 2 -> let [ty1,ty2] = tys in retArrowType ATType ty1 ty2
                                        | tyCon == listTyCon -> RetAtom $ tyChar '[' <> (case tys of
                                                                                           []  -> empty
                                                                                           t:_ -> normalExpr t) <> tyChar ']'
                                        | isTupleTyCon tyCon -> RetAtom $ tyChar '(' <> (if null tys
                                                                                         then empty
                                                                                         else foldr1 (\ ty r -> ty <> tyChar ',' <+> r) (map normalExpr tys)
                                                                                        )
                                                                                     <> tyChar ')'
                                        | isLiftedTypeKindCon tyCon -> RetAtom $ tyChar '*'
                                        | otherwise                 -> retApps pCon tys
              )

--------------------------------------------------------------------

ppCoercion :: PrettyH Coercion
ppCoercion = ppCoercionR >>^ normalExpr

ppCoercionModeR :: Transform PrettyC HermitM Coercion RetExpr
ppCoercionModeR = do opts <- prettyC_options ^<< contextT
                     case po_coercions opts of
                       Omit     -> return RetEmpty
                       Abstract -> return (RetAtom coercionSymbol)
                       Kind     -> ppCoKind >>^ (\ k -> RetExpr (coercionSymbol <+> coTypeSymbol <+> k))
                       _        -> ppCoercionR

ppCoercionR :: Transform PrettyC HermitM Coercion RetExpr
ppCoercionR =
    coVarCoT (RetAtom <$> ppVarOcc)
 <+ symCoT (ppCoercionR >>> parenExpr >>^ \ co -> RetExpr (coKeyword "sym" <+> co))
 <+ subCoT (ppCoercionR >>> parenExpr >>^ \ co -> RetExpr (coKeyword "sub" <+> co))
 <+ forAllCoT ppBinderMode ppCoercionR retForAll
 <+ transCoT (ppCoercionR >>> parenExprExceptApp) (ppCoercionR >>> parenExprExceptApp) (\ co1 co2 -> RetExpr (co1 <+> coChar ';' <+> co2))
 <+ nthCoT (arr show) (ppCoercionR >>> parenExpr) (\ n co -> RetExpr (coKeyword "nth" <+> coText n <+> co))
 <+ instCoT (ppCoercionR >>> parenExpr &&& parenExprExceptApp) (ppTypeModeR >>> parenExprExceptApp) (\ (cop1,cop2) ty -> if isEmpty ty
                                                                                                                         then RetExpr (coText "inst" <+> cop1)
                                                                                                                         else RetExpr (cop2 <+> coChar '@' <+> ty)
                                                                                                    )
 <+ appCoT ppCoercionR ppCoercionR retApp
 -- TODO: Figure out how to properly pp new branched Axioms and Left/Right Coercions
 <+ reflT (ppTypeModeR >>^ normalExpr) (\ r ty -> RetAtom $ if isEmpty ty then coText "refl" else coChar '<' <> coText (showRole r ++ ":") <> ty <> coChar '>')
 <+ tyConAppCoT (forkFirst ppTyConCo) (const ppCoercionR)
                (\ r (ptc, tc) cs -> if isFunTyCon tc && (length cs == 2)
                                     then let [c1,c2] = cs
                                            in retArrowType ATCoercion c1 c2
                                     else retApps (coText (showRole r ++ ":") <> ptc) cs)
 <+ axiomInstCoT (coAxiomName ^>> ppName CoercionColor) ppSDoc (\ _ -> ppCoercionR >>> parenExpr) (\ ax idx coes -> RetExpr (coText "axiomInst" <+> ax <+> idx <+> sep coes))
 <+ lrCoT ppSDoc (ppCoercionR >>> parenExpr) (\ lr co -> RetExpr (coercionColor lr <+> co))
 
 <+ univCoT (ppTypeModeR >>^ normalExpr) (ppTypeModeR >>^ normalExpr)
            (\ s r dom ran -> RetExpr (coKeyword "univ" <+> coText (show s) <+> coText (showRole r) <+> dom <+> ran)) -- retApps?


 <+ constT (return . RetAtom $ text "Unsupported Coercion Constructor")

ppCoKind :: PrettyH Coercion
ppCoKind = do
    (r, Pair co1 co2) <- arr (coercionRole &&& coercionKind)
    ty1 <- return co1 >>> ppTypeModeR >>> parenExprExceptApp
    ty2 <- return co2 >>> ppTypeModeR >>> parenExprExceptApp
    return $ cat [ty1, pad (coText ("~" ++ showRole r)), ty2]

--------------------------------------------------------------------

ppTypeSig :: PrettyH CoreExpr
ppTypeSig = coercionT ppCoKind <+ (exprKindOrType ^>> ppKindOrType)

------------------------------------------------------------------------------------------------
