{-# LANGUAGE CPP, LambdaCase, MultiWayIf #-}

module Language.HERMIT.PrettyPrinter.Clean
  ( -- * HERMIT's Clean Pretty-Printer for GHC Core
    corePrettyH
  )
where

import Control.Arrow hiding ((<+>))
import Control.Applicative ((<$>))

import Data.List (intersperse)
import Data.Char (isSpace)
import Data.Set (notMember)

import GhcPlugins (TyCon(..), Coercion(..), Var(..), Expr(..))
import qualified GhcPlugins as GHC

import Language.HERMIT.Context
import Language.HERMIT.Core
import Language.HERMIT.GHC
import Language.HERMIT.Kure
import Language.HERMIT.Monad
import Language.HERMIT.Syntax

import Language.HERMIT.PrettyPrinter.Common

import Language.HERMIT.Primitive.Common

import Pair

import Text.PrettyPrint.MarkedHughesPJ as PP

------------------------------------------------------------------------------------------------

data RetExpr
        = RetLam AbsolutePathH [DocH] AbsolutePathH DocH
        | RetLet AbsolutePathH [DocH] AbsolutePathH DocH
        | RetApp DocH [RetExpr]
        | RetForAll AbsolutePathH [DocH] AbsolutePathH DocH
        | RetArrowType [DocH] -- TODO: store PathH here to mark arrows
        | RetExpr DocH
        | RetAtom DocH         -- parens not needed
        | RetEmpty

retApp :: RetExpr -> RetExpr -> RetExpr
retApp f             RetEmpty = f
retApp RetEmpty      e        = e
retApp (RetApp f es) e        = RetApp f (es ++ [e])
retApp f             e        = RetApp (parenExpr f) [e]

retApps :: RetExpr -> [RetExpr] -> RetExpr
retApps = foldl retApp

retLam :: AbsolutePathH -> RetExpr -> RetExpr -> RetExpr
retLam _ RetEmpty e            = e
retLam p v (RetLam _ vs pb e)  = RetLam p (parenExpr v : vs) pb e
retLam p v e                   = RetLam p [parenExpr v] (p @@ Lam_Body) (normalExpr e)

retLet :: AbsolutePathH -> RetExpr -> RetExpr -> RetExpr
retLet _ RetEmpty body                    = body
retLet p bnd      (RetLet _ bnds pb body) = RetLet p (normalExpr bnd : bnds) pb body
retLet p bnd      body                    = RetLet p [normalExpr bnd] (p @@ Let_Body) (normalExpr body)

retForAll :: AbsolutePathH -> Crumb -> RetExpr -> RetExpr -> RetExpr
retForAll _ _ RetEmpty ty                      = ty
retForAll p _  v       (RetForAll _ vs pb ty)  = RetForAll p (parenExpr v : vs) pb ty
retForAll p cr v       ty                      = RetForAll p [parenExpr v] (p @@ cr) (normalExpr ty)

retArrowType :: RetExpr -> RetExpr -> RetExpr
retArrowType ty1 (RetArrowType tys) = RetArrowType (parenExprExceptApp ty1 : tys)
retArrowType ty1 ty2                = RetArrowType [parenExprExceptApp ty1, parenExprExceptApp ty2]

------------------------------------------------------------------------------------------------

isEmptyR :: RetExpr -> Bool
isEmptyR RetEmpty = True
isEmptyR _        = False

isAtom :: RetExpr -> Bool
isAtom (RetAtom _) = True
isAtom _           = False

------------------------------------------------------------------------------------------------

normalExpr :: RetExpr -> DocH
normalExpr  RetEmpty           = empty
normalExpr (RetAtom e)         = e
normalExpr (RetExpr e)         = e
normalExpr (RetLam p vs pb e)  = hang (attrP p (specialSymbol LambdaSymbol) <+> hsep vs <+> attrP pb (specialSymbol RightArrowSymbol)) 2 e
normalExpr (RetLet p vs pb e)  = sep [ attrP p (keyword "let") <+> vcat vs, attrP pb (keyword "in") <+> e ]
normalExpr (RetApp f es)       = let (atoms,exprs) = span isAtom es
                                  in sep [ hsep (f : map normalExpr atoms)
                                         , nest 2 (sep $ map parenExpr exprs) ]
normalExpr (RetForAll p vs pb ty) = attrP p (specialSymbol ForallSymbol) <+> hsep vs <+> attrP pb (symbol '.') <+> ty
normalExpr (RetArrowType tys)     = hsep (intersperse typeArrow tys)

parenExpr :: RetExpr -> DocH
parenExpr RetEmpty      = empty
parenExpr (RetAtom e)   = e
parenExpr (RetApp d []) = d
parenExpr other         = ppParens (normalExpr other)

parenExprExceptApp :: RetExpr -> DocH
parenExprExceptApp e@(RetApp _ _) = normalExpr e
parenExprExceptApp e              = parenExpr e

------------------------------------------------------------------------------------------------

attrPAtomExpr :: AbsolutePathH -> RetExpr -> RetExpr
attrPAtomExpr p (RetAtom d) = RetAtom (attrP p d)
attrPAtomExpr p (RetExpr d) = RetExpr (attrP p d)
attrPAtomExpr _ e           = e

------------------------------------------------------------------------------------------------

ppParens :: DocH -> DocH
ppParens p = symbol '(' <> p <> symbol ')'

------------------------------------------------------------------------------------------------

specialSymbol :: SpecialSymbol -> DocH
specialSymbol = markColor SyntaxColor . specialFont . char . renderSpecial

symbol :: Char -> DocH
symbol = markColor SyntaxColor . char

keyword :: String -> DocH
keyword = markColor KeywordColor . text


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


tySymbol :: SpecialSymbol -> DocH
tySymbol = typeColor . specialFont . char . renderSpecial

typeSymbol :: DocH
typeSymbol = tySymbol TypeSymbol

typeBindSymbol :: DocH
typeBindSymbol = tySymbol TypeBindSymbol

typeArrow :: DocH
typeArrow = tySymbol RightArrowSymbol

------------------------------------------------------------------------------------------------

hasType :: DocH -> DocH -> DocH
e `hasType` ty = e <+> tySymbol TypeOfSymbol <+> ty

------------------------------------------------------------------------------------------------

-- TODO: PrettyOptions should be in the context.

-- | Pretty print a fragment of GHC Core using HERMIT's \"Clean\" pretty printer.
corePrettyH :: PrettyOptions -> PrettyH CoreTC
corePrettyH opts =
    let
        -- Use for any GHC structure
        ppSDoc :: GHC.Outputable a => PrettyH a
        ppSDoc = do dynFlags <- constT GHC.getDynFlags
                    arr (toDoc . GHC.showSDoc dynFlags . GHC.ppr)
            where toDoc s | any isSpace s = parens (text s)
                          | otherwise     = text s

        ppVar :: Translate PrettyC HermitM Var RetExpr
        ppVar = readerT $ \ v -> GHC.varName ^>> ppName (varColor v)

        varColor :: Var -> SyntaxForColor
        varColor var | GHC.isTyVar var = TypeColor
                     | GHC.isCoVar var = CoercionColor
                     | otherwise       = IdColor

        ppName :: SyntaxForColor -> Translate PrettyC HermitM GHC.Name RetExpr
        ppName color = (GHC.nameOccName >>> GHC.occNameString) ^>> arr (\ name -> let doc  = markColor color (text name)
                                                                                           -- TODO: is "isScriptInfixId" the right predicate to use here?
                                                                                   in RetAtom $ if all isScriptInfixIdChar name
                                                                                                 then ppParens doc
                                                                                                 else doc
                                                                       )

        ppLitTy :: Translate PrettyC HermitM TyLit RetExpr
        ppLitTy = arr $ \case
                          NumTyLit i  -> RetAtom $ tyText (show i)
                          StrTyLit fs -> RetAtom $ tyText (show fs)

        ppTyCon :: Translate PrettyC HermitM TyCon RetExpr
        ppTyCon = GHC.getName ^>> ppName TypeColor

        ppTyConCo :: Translate PrettyC HermitM TyCon RetExpr
        ppTyConCo = GHC.getName ^>> ppName CoercionColor

        -- binders are vars that is bound by lambda or case, etc.
        -- depending on the mode, they might not be displayed
        ppBinderMode :: Translate PrettyC HermitM Var RetExpr
        ppBinderMode = do v <- idR
                          if
                             | GHC.isTyVar v -> case po_exprTypes opts of
                                                                   Omit     -> return (RetEmpty)
                                                                   Abstract -> return (RetAtom typeBindSymbol)
                                                                   _        -> ppVar
                             | GHC.isCoVar v -> case po_coercions opts of
                                                                   Omit     -> return (RetEmpty)
                                                                   Abstract -> return (RetAtom coercionBindSymbol)
                                                                   Show     -> ppVar
                                                                   Kind     -> do pCoKind <- ppCoKind <<^ CoVarCo
                                                                                  return (RetExpr (coercionBindSymbol `hasType` pCoKind))
                                                                  -- TODO: refactor this to be more systematic.  It should be possible to request type sigs for all type bindings.
                             | otherwise       -> ppVar

        ppModGuts :: PrettyH GHC.ModGuts
        ppModGuts = do name <- ppSDoc <<^ GHC.mg_module
                       vtys <- mapT (ppVar &&& (ppType <<^ GHC.idType)) <<< modGutsT progIdsT (\ _ ids -> ids)
                       let defs = [ normalExpr v `hasType` ty | (v,ty) <- vtys ]
                       return $ hang (keyword "module" <+> name <+> keyword "where") 2 (vcat defs)

        -- DocH is not a monoid.
        ppCoreProg :: PrettyH CoreProg
        ppCoreProg = progConsT ppCoreBind ppCoreProg ($+$) <+ progNilT empty

        ppCoreBind :: PrettyH GHC.CoreBind
        ppCoreBind =   (nonRecT idR (ppCoreExprR &&& ppTypeSig) (,) >>> ppDef)
                    <+ (do p <- absPathT
                           recT (const ppCoreDef) (\ bnds -> attrP p (keyword "rec") <+> vcat bnds)
                       )


        ppCoreAlt :: PrettyH GHC.CoreAlt
        ppCoreAlt = do p <- absPathT
                       altT (readerT $ \case
                                          GHC.DataAlt dcon -> return (GHC.dataConName dcon) >>> ppName IdColor >>^ parenExpr
                                          GHC.LitAlt lit   -> return lit >>> ppSDoc
                                          GHC.DEFAULT      -> return (symbol '_')
                            )
                            (\ _ -> ppBinderMode)
                            ppCoreExpr
                            (\ con vs e -> hang (con <+> hsep (map parenExpr vs) <+> attrP p (specialSymbol RightArrowSymbol)) 2 e)

        ppCoreDef :: PrettyH CoreDef
        ppCoreDef = defT idR (ppCoreExprR &&& ppTypeSig) (,) >>> ppDef

        ppDef :: PrettyH (Var,(RetExpr,DocH))
        ppDef = do p          <- absPathT
                   (v,(e,ty)) <- idR
                   case po_coercions opts of
                     Omit | GHC.isCoVar v  -> return empty
                     Kind | GHC.isCoVar v  -> return $ case po_exprTypes opts of
                                                         Show -> (coercionBindSymbol `hasType` ty) $+$ (coercionBindSymbol <+> symbol '=' <+> coercionSymbol)
                                                         _    -> coercionBindSymbol <+> attrP p (symbol '=') <+> normalExpr e
                     _                     -> do pv  <- normalExpr ^<< ppBinderMode <<< return v
                                                 let pre  = pv <+> symbol '='
                                                     body = case e of -- This is an ugly hack
                                                              RetLam p' vs pb e0 -> hang (pre <+> attrP p' (specialSymbol LambdaSymbol) <+> hsep vs <+> attrP pb (specialSymbol RightArrowSymbol)) 2 e0
                                                              _                 -> hang pre 2 (normalExpr e)
                                                 return $ case po_exprTypes opts of
                                                            Omit | GHC.isTyVar v -> empty
                                                            Show                 -> (pv `hasType` ty) $+$ body
                                                            _                    -> body


        ppCoreExpr :: PrettyH GHC.CoreExpr
        ppCoreExpr = ppCoreExprR >>^ normalExpr

        ppCoreExprR :: Translate PrettyC HermitM GHC.CoreExpr RetExpr
        ppCoreExprR = absPathT >>= ppCoreExprPR
          where
            ppCoreExprPR :: AbsolutePathH -> Translate PrettyC HermitM GHC.CoreExpr RetExpr
            ppCoreExprPR p =
                      lamT ppBinderMode ppCoreExprR (retLam p)

                   <+ letT (RetExpr <$> ppCoreBind) ppCoreExprR (retLet p)
                   -- HACKs
    {-
                   <+ (acceptR (\ e -> case e of
                                         GHC.App (Var v) (GHC.Type t) | po_exprTypes opts == Abstract -> True
                                         _ -> False) >>>
                               (appT ppCoreExprR ppCoreExprR (\ (RetAtom e1) (RetAtom e2) ->
                                        RetAtom (e1 <+> e2))))
    -}
                   <+ (acceptR (\ e -> case e of
                                         App (Type _) (Lam {}) | po_exprTypes opts == Omit -> True
                                         App (App (Var _) (Type _)) (Lam {}) | po_exprTypes opts == Omit -> True
                                         _ -> False) >>>
                               (appT ppCoreExprR ppCoreExprR (\ (RetAtom e1) (RetLam p' vs pb e0) ->
                                        RetExpr $ hang (e1 <+>
                                                            symbol '(' <>
                                                            attrP p' (specialSymbol LambdaSymbol) <+>
                                                            hsep vs <+>
                                                            attrP pb (specialSymbol RightArrowSymbol)) 2 (e0 <> symbol ')')))
                      )

                   <+ appT ppCoreExprR ppCoreExprR retApp
                   <+ caseT ppCoreExpr ppVar ppTypeModeR (const ppCoreAlt) (\ s w ty alts -> RetExpr $ attrP p ((keyword "case" <+> s <+> keyword "of" <+> parenExpr w <+> parenExpr ty) $$ nest 2 (vcat alts)))

                   <+ varT (attrPAtomExpr p <$> (do (c,i) <- exposeT
                                                    if (GHC.isLocalId i) && (i `notMember` boundVars c)
                                                      then GHC.varName ^>> ppName WarningColor
                                                      else ppVar
                                                )
                           )

                   <+ litT ((RetAtom . attrP p) <$> ppSDoc)
                   <+ typeT (attrPAtomExpr p <$> ppTypeModeR)
                   <+ coercionT (attrPAtomExpr p <$> ppCoercionModeR)
                   <+ castT ppCoreExprR ppCoercionModeR (\ e co -> if isEmptyR co
                                                                    then e
                                                                    else RetExpr (parenExprExceptApp e <+> attrP p castSymbol <+> parenExprExceptApp co)
                                                        )
                   <+ tickT ppSDoc ppCoreExprR (\ tk e -> RetExpr $ attrP p (text "Tick" $$ nest 2 (tk <+> parenExpr e)))

        --------------------------------------------------------------------

        ppType :: PrettyH Type
        ppType = ppTypeR >>^ normalExpr

        ppTypeModeR :: Translate PrettyC HermitM Type RetExpr
        ppTypeModeR = case po_exprTypes opts of
                        Omit     -> return RetEmpty
                        Abstract -> return (RetAtom typeSymbol)
                        _        -> ppTypeR

        ppTypeR :: Translate PrettyC HermitM Type RetExpr
        ppTypeR = absPathT >>= ppTypePR
          where
            ppTypePR :: AbsolutePathH -> Translate PrettyC HermitM Type RetExpr
            ppTypePR p =
                   tyVarT (attrPAtomExpr p <$> ppVar)
                <+ litTyT (attrPAtomExpr p <$> ppLitTy)
                <+ appTyT ppTypeR ppTypeR retApp
                <+ funTyT ppTypeR ppTypeR retArrowType
                <+ forAllTyT ppVar ppTypeR (retForAll p ForAllTy_Body)
                <+ tyConAppT (ppTyCon &&& idR) (const ppTypeR)
                     (\ (pCon,tyCon) tys -> if | GHC.isFunTyCon tyCon && length tys == 2 -> let [ty1,ty2] = tys in retArrowType ty1 ty2
                                               | tyCon == GHC.listTyCon -> RetAtom $ attrP p $ tyText "[" <> (case tys of
                                                                                                                []  -> empty
                                                                                                                t:_ -> normalExpr t)
                                                                                                          <> tyText "]"
                                               | GHC.isTupleTyCon tyCon -> RetAtom $ attrP p $ tyText "(" <> (if null tys
                                                                                                                then empty
                                                                                                                else foldr1 (\ ty r -> ty <> tyText "," <+> r) (map normalExpr tys)
                                                                                                             )
                                                                                                          <> tyText ")"
                                               | otherwise              -> retApps (attrPAtomExpr p pCon) tys
                     )

        --------------------------------------------------------------------

        ppCoercion :: PrettyH Coercion
        ppCoercion = ppCoercionR >>^ normalExpr

        ppCoercionModeR :: Translate PrettyC HermitM Coercion RetExpr
        ppCoercionModeR = case po_coercions opts of
                            Omit     -> return RetEmpty
                            Abstract -> return (RetAtom coercionSymbol)
                            Show     -> ppCoercionR
                            Kind     -> ppCoKind >>^ (\ k -> RetExpr (coercionSymbol `hasType` k))

        ppCoercionR :: Translate PrettyC HermitM Coercion RetExpr
        ppCoercionR = absPathT >>= ppCoercionPR
          where
            ppCoercionPR :: AbsolutePathH -> Translate PrettyC HermitM Coercion RetExpr
            ppCoercionPR p =
                           reflT (ppTypeModeR >>^ \ ty -> RetAtom $ attrP p $ if isEmptyR ty then coText "refl" else coText "<" <> normalExpr ty <> coText ">")
                        <+ coVarCoT (attrPAtomExpr p <$> ppVar)
                        <+ symCoT (ppCoercionR >>^ \ co -> RetExpr (attrP p (coKeyword "sym") <+> parenExpr co))
                        <+ forAllCoT ppBinderMode ppCoercionR (retForAll p ForAllCo_Body)
                        <+ transCoT ppCoercionR ppCoercionR (\ co1 co2 -> RetExpr (parenExprExceptApp co1 <+> attrP p (coChar ';') <+> parenExprExceptApp co2))
                        <+ unsafeCoT ppTypeModeR ppTypeModeR (\ ty1 ty2 -> (if isEmptyR ty1 && isEmptyR ty2 then RetAtom else RetExpr)
                                                                           (attrP p (coKeyword "unsafe") <+> parenExpr ty1 <+> parenExpr ty2)
                                                             )
                        <+ nthCoT idR ppCoercionR (\ n co -> RetExpr (attrP p (coKeyword "nth") <+> attrP p (coText $ show n) <+> parenExpr co))
                        <+ instCoT ppCoercionR ppTypeModeR (\ co ty -> if isEmptyR ty
                                                                         then RetExpr (attrP p (coText "inst") <+> parenExpr co)
                                                                         else RetExpr (parenExprExceptApp co <+> attrP p (coChar '@') <+> parenExprExceptApp ty)
                                                           )
                        <+ tyConAppCoT (attrPAtomExpr p <$> ppTyConCo) (const ppCoercionR) retApps
                        <+ appCoT ppCoercionR ppCoercionR retApp
#if __GLASGOW_HASKELL__ > 706
        -- TODO: Figure out how to properly pp new branched Axioms and Left/Right Coercions
                        <+ axiomInstCoT (coAxiomName ^>> ppName CoercionColor) (arr $ RetAtom . ppSDoc) (const ppCoercionR) (\ ax idx coes -> RetExpr (attrP p (coText "axiomInst") <+> attrP p (parenExpr ax) <+> attrP p (parenExpr idx) <+> sep (map parenExpr coes)))
                        <+ lrCoT (arr (coercionColor . ppSDoc)) ppCoercionR (\ lr co -> RetExpr (attrP p lr <+> parenExpr co))
#else
                        <+ axiomInstCoT (coAxiomName ^>> ppName CoercionColor) (const ppCoercionR) (\ ax coes -> RetExpr (attrP p (coText "axiomInst") <+> attrP p (parenExpr ax) <+> sep (map parenExpr coes)))
#endif

        ppCoKind :: PrettyH Coercion
        ppCoKind = (GHC.coercionKind >>> unPair) ^>> (ppTypeModeR *** ppTypeModeR) >>^ ( \(ty1,ty2) -> parenExprExceptApp ty1 <+> coText "~#" <+> parenExprExceptApp ty2)

        --------------------------------------------------------------------

        ppTypeSig :: PrettyH GHC.CoreExpr
        ppTypeSig = coercionT ppCoKind <+ (GHC.exprType ^>> ppType)

        --------------------------------------------------------------------

    in  promoteT (ppCoreExpr     :: PrettyH GHC.CoreExpr)
     <+ promoteT (ppCoreProg     :: PrettyH CoreProg)
     <+ promoteT (ppCoreBind     :: PrettyH GHC.CoreBind)
     <+ promoteT (ppCoreDef      :: PrettyH CoreDef)
     <+ promoteT (ppModGuts      :: PrettyH GHC.ModGuts)
     <+ promoteT (ppCoreAlt      :: PrettyH GHC.CoreAlt)
     <+ promoteT (ppType         :: PrettyH GHC.Type)
     <+ promoteT (ppCoercion     :: PrettyH Coercion)

------------------------------------------------------------------------------------------------
