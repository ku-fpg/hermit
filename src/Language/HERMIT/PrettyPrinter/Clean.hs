module Language.HERMIT.PrettyPrinter.Clean
  ( -- * HERMIT's Clean Pretty-Printer for GHC Core
    corePrettyH
  )
where

import Control.Monad (ap)
import Control.Arrow hiding ((<+>))

import Data.Char (isSpace)
import Data.Traversable (sequenceA)

import qualified GhcPlugins as GHC

import Language.HERMIT.Syntax
import Language.HERMIT.Kure
import Language.HERMIT.Core
import Language.HERMIT.PrettyPrinter.Common
import Language.HERMIT.GHC

import TypeRep (TyLit(..))

import Text.PrettyPrint.MarkedHughesPJ as PP

------------------------------------------------------------------------------------------------

data RetExpr
        = RetLam [DocH] DocH
        | RetLet [DocH] DocH
        | RetApp DocH [RetExpr]
        | RetExpr DocH
        | RetAtom DocH         -- parens not needed
        | RetEmpty

isAtom :: RetExpr -> Bool
isAtom (RetAtom _) = True
isAtom _           = False

specialSymbol :: SpecialSymbol -> DocH
specialSymbol = markColor SyntaxColor . specialFont . char . renderSpecial

symbol :: Char -> DocH
symbol = markColor SyntaxColor . char

keyword :: String -> DocH
keyword = markColor KeywordColor . text

ppParens :: DocH -> DocH
ppParens p = symbol '(' <> p <> symbol ')' -- :: markColor SyntaxColor

atomExpr :: RetExpr -> DocH
atomExpr (RetAtom e) = e
atomExpr other       = ppParens (normalExpr other)

normalExpr :: RetExpr -> DocH
normalExpr (RetLam vs e0) = hang (specialSymbol LambdaSymbol <+> hsep vs <+> specialSymbol RightArrowSymbol) 2 e0
normalExpr (RetLet vs e0) = sep [ keyword "let" <+> vcat vs, keyword "in" <+> e0 ]
normalExpr (RetApp fn xs) = sep [ hsep (fn : map atomExpr (takeWhile isAtom xs))
                                , nest 2 (sep (map atomExpr (dropWhile isAtom xs))) ]
normalExpr (RetExpr e0)    = e0
normalExpr (RetAtom e0)    = e0
normalExpr (RetEmpty)      = empty

castSymbol :: DocH
castSymbol = markColor CoercionColor (specialFont $ char $ renderSpecial CastSymbol)

coercionSymbol :: DocH
coercionSymbol = markColor CoercionColor (specialFont $ char $ renderSpecial CoercionSymbol)

coercionBindSymbol :: DocH
coercionBindSymbol = markColor CoercionColor (specialFont $ char $ renderSpecial CoercionBindSymbol)

typeSymbol :: DocH
typeSymbol = markColor TypeColor (specialFont $ char $ renderSpecial TypeSymbol)

typeBindSymbol :: DocH
typeBindSymbol = markColor TypeColor (specialFont $ char $ renderSpecial TypeBindSymbol)

------------------------------------------------------------------------------------------------

-- | Pretty print a fragment of GHC Core using HERMIT's \"Clean\" pretty printer.
corePrettyH :: PrettyOptions -> PrettyH Core
corePrettyH opts = do
    dynFlags <- constT GHC.getDynFlags

    let hideNotes = True

        optional :: Maybe DocH -> (DocH -> DocH) -> DocH
        optional Nothing  _ = empty
        optional (Just d) k = k d

        ppVar :: GHC.Var -> DocH
        ppVar v = ppName (varColor v) (GHC.varName v)

        varColor :: GHC.Var -> SyntaxForColor
        varColor var | GHC.isTyVar var = TypeColor
                     | GHC.isCoVar var = CoercionColor
                     | otherwise       = IdColor

        ppName :: SyntaxForColor -> GHC.Name -> DocH
        ppName color nm  = let name = GHC.occNameString (GHC.nameOccName nm)
                               doc  = markColor color (text name)
                            in if all isInfixId name
                                then ppParens doc
                                else doc

        ppLitTy :: TyLit -> DocH
        ppLitTy tylit = typeColor $ text $ case tylit of
                                             NumTyLit i  -> show i
                                             StrTyLit fs -> show fs

        -- binders are vars that is bound by lambda or case, etc.
        ppBinder :: GHC.Var -> Maybe DocH
        ppBinder var | GHC.isTyVar var = case po_exprTypes opts of
                                            Abstract -> Just $ typeBindSymbol
                                            Omit     -> Nothing
                                            _        -> Just $ ppVar var
                     | GHC.isCoVar var = case po_exprTypes opts of
                                            Abstract -> Just $ coercionBindSymbol
                                            Omit     -> Nothing
                                            _        -> Just $ ppVar var
                     | otherwise = Just $ ppVar var

        -- Use for any GHC structure, the 'showSDoc' prefix is to remind us
        -- that we are eliding infomation here.
        ppSDoc :: (GHC.Outputable a) => a -> MDoc b
        ppSDoc = toDoc . (if hideNotes then id else ("showSDoc: " ++)) . GHC.showSDoc dynFlags . GHC.ppr
            where toDoc s | any isSpace s = parens (text s)
                          | otherwise     = text s

        ppModGuts :: PrettyH GHC.ModGuts
        ppModGuts =   arr $ \ m -> hang (keyword "module" <+> ppSDoc (GHC.mg_module m) <+> keyword "where") 2
                                   (vcat [ (optional (ppBinder v) (\b -> b <+> specialSymbol TypeOfSymbol <+> normalExpr (ppCoreType (GHC.idType v))))
                                         | bnd <- GHC.mg_binds m
                                         , v <- case bnd of
                                                  GHC.NonRec f _ -> [f]
                                                  GHC.Rec bnds -> map fst bnds
                                       ])

        -- DocH is not a monoid.
        -- GHC uses a list, which we print here. The CoreProg type is our doing.
        ppCoreProg :: PrettyH CoreProg
        ppCoreProg = translate $ \ c -> fmap vcat . sequenceA . map (apply ppCoreBind c) . progToBinds

        ppCoreExpr :: PrettyH GHC.CoreExpr
        ppCoreExpr = ppCoreExprR >>^ normalExpr

        appendArg xs (RetEmpty) = xs
        appendArg xs e          = xs ++ [e]

        appendBind Nothing  xs = xs
        appendBind (Just v) xs = v : xs

        ppCoreExprR :: TranslateH GHC.CoreExpr RetExpr
        ppCoreExprR = ppCoreExprPR `ap` rootPathT

        ppCoreExprPR :: TranslateH GHC.CoreExpr (Path -> RetExpr)
        ppCoreExprPR = lamT ppCoreExprR (\ v e _ -> case e of
                                                  RetLam vs e0  -> RetLam (appendBind (ppBinder v) vs) e0
                                                  _             -> RetLam (appendBind (ppBinder v) []) (normalExpr e))

                   <+ letT ppCoreBind ppCoreExprR
                                       (\ bd e _ -> case e of
                                                  RetLet vs e0  -> RetLet (bd : vs) e0
                                                  _             -> RetLet [bd] (normalExpr e))
                   -- HACKs
    {-
                   <+ (acceptR (\ e -> case e of
                                         GHC.App (GHC.Var v) (GHC.Type t) | po_exprTypes opts == Abstract -> True
                                         _ -> False) >>>
                               (appT ppCoreExprR ppCoreExprR (\ (RetAtom e1) (RetAtom e2) ->
                                        RetAtom (e1 <+> e2))))
    -}
                   <+ (acceptR (\ e -> case e of
                                         GHC.App (GHC.Type _) (GHC.Lam {}) | po_exprTypes opts == Omit -> True
                                         GHC.App (GHC.App (GHC.Var _) (GHC.Type _)) (GHC.Lam {}) | po_exprTypes opts == Omit -> True
                                         _ -> False) >>>
                               (appT ppCoreExprR ppCoreExprR (\ (RetAtom e1) (RetLam vs e0) _ ->
                                        RetExpr $ hang (e1 <+>
                                                            symbol '(' <>
                                                            specialSymbol LambdaSymbol <+>
                                                            hsep vs <+>
                                                            specialSymbol RightArrowSymbol) 2 (e0 <> symbol ')')))


                      )

                   <+ appT ppCoreExprR ppCoreExprR
                                       (\ e1 e2 _ -> case e1 of
                                                  RetApp f xs   -> RetApp f (appendArg xs e2)
                                                  _             -> case e2 of -- if our only args are types, and they are omitted, don't paren
                                                                    RetEmpty -> e1
                                                                    args -> RetApp (atomExpr e1) (appendArg [] args))
                   <+ caseT ppCoreExpr (const ppCoreAlt) (\ s b _ alts p -> RetExpr $ attrP p ((keyword "case" <+> s <+> keyword "of" <+> optional (ppBinder b) id) $$ nest 2 (vcat alts)))
                   <+ varT (\ i p -> RetAtom (attrP p $ ppVar i))
                   <+ litT (\ i p -> RetAtom (attrP p $ ppSDoc i))
                   <+ typeT (\ t p -> case po_exprTypes opts of
                                      Show     -> case ppCoreType t of
                                                    RetAtom d -> RetAtom $ attrP p d
                                                    RetExpr d -> RetExpr $ attrP p d
                                                    _         -> error "not possible!"
                                      Abstract -> RetAtom (attrP p typeSymbol)
                                      Omit     -> RetEmpty)
                   <+ coercionT ppCoreCoercion
                   <+ castT ppCoreExprR (\ e co p -> let e' = case e of
                                                                RetAtom a -> a
                                                                _         -> ppParens (normalExpr e)
                                                      in case ppCoreCoercion co p of
                                                           RetEmpty    -> e
                                                           RetAtom pCo -> RetExpr $ attrP p (e' <+> castSymbol <+> pCo)
                                                           pCo         -> RetExpr $ attrP p (e' <+> castSymbol <+> ppParens (normalExpr pCo))
                                                     )
                   <+ tickT ppCoreExpr (\ i e p -> RetExpr $ attrP p (text "Tick" $$ nest 2 (ppSDoc i <+> parens e)))


        ppCoreType :: GHC.Type -> RetExpr
        ppCoreType = go
            where go (TyVarTy v)   = RetAtom $ ppVar v
                  go (LitTy tylit) = RetAtom $ ppLitTy tylit
                  go (AppTy t1 t2) = RetExpr $ normalExpr (go t1) <+> normalExpr (go t2)
                  go (TyConApp tyCon tys)
                    | GHC.isFunTyCon tyCon, [ty1,ty2] <- tys = go (FunTy ty1 ty2)
                    | tyCon == GHC.listTyCon = RetAtom $ tyText "[" <> (case map (normalExpr . go) tys of
                                                                            []    -> empty
                                                                            (t:_) -> t) <> tyText "]"
                    | GHC.isTupleTyCon tyCon = case map (normalExpr . go) tys of
                                                [] -> RetAtom $ tyText "()"
                                                ds -> RetAtom $ tyText "(" <> (foldr1 (\d r -> d <> tyText "," <+> r) ds) <> tyText ")"
                    | otherwise = RetAtom $ ppName TypeColor (GHC.getName tyCon) <+> sep (map (normalExpr . go) tys) -- has spaces, but we never want parens
                  go (FunTy ty1 ty2) = RetExpr $ atomExpr (go ty1) <+> tyText "->" <+> normalExpr (go ty2)
                  go (ForAllTy v ty) = RetExpr $ specialSymbol ForallSymbol <+> ppVar v <+> symbol '.' <+> normalExpr (go ty)

                  tyText = typeColor . text

        ppCoreCoercion :: GHC.Coercion -> Path -> RetExpr
        ppCoreCoercion co p = case po_exprTypes opts of
                                             Show     -> RetExpr $ attrP p (coercionColor $ nest 2 $ ppSDoc co) -- TODO: improve this
                                             Abstract -> RetAtom $ attrP p coercionSymbol
                                             Omit     -> RetEmpty

        ppCoreTypeSig :: PrettyH GHC.CoreExpr
        ppCoreTypeSig = arr $ normalExpr . ppCoreType . GHC.exprType

        ppCoreBind :: PrettyH GHC.CoreBind
        ppCoreBind = nonRecT (ppCoreExprR &&& ppCoreTypeSig) ppDefFun
                  <+ recT (const ppCoreDef) (\ bnds -> keyword "rec" <+> vcat bnds)

        ppCoreAlt :: PrettyH GHC.CoreAlt
        ppCoreAlt = altT ppCoreExpr $ \ con vs e -> let ppVars = if null vs
                                                                  then specialSymbol RightArrowSymbol
                                                                  else hsep (map (flip optional id . ppBinder) vs) <+> specialSymbol RightArrowSymbol
                                                     in case con of
                      GHC.DataAlt dcon -> hang (ppName IdColor (GHC.dataConName dcon) <+> ppVars) 2 e
                      GHC.LitAlt lit   -> hang (ppSDoc lit <+> ppVars) 2 e
                      GHC.DEFAULT      -> symbol '_' <+> ppVars <+> e

        -- GHC uses a tuple, which we print here. The CoreDef type is our doing.
        ppCoreDef :: PrettyH CoreDef
        ppCoreDef = defT (ppCoreExprR &&& ppCoreTypeSig) ppDefFun

        ppDefFun :: GHC.Var -> (RetExpr, DocH) -> DocH
        ppDefFun v (e,ty) = case po_exprTypes opts of
                                Show -> (ppVar v <+> specialSymbol TypeOfSymbol <+> ty) $+$ body
                                _    -> body
            where
                pre = optional (ppBinder v) (<+> symbol '=')
                body = case e of
                        RetLam vs e0 -> hang (pre <+> specialSymbol LambdaSymbol <+> hsep vs <+> specialSymbol RightArrowSymbol) 2 e0
                        _ -> hang pre 2 (normalExpr e)

    promoteT (ppCoreExpr :: PrettyH GHC.CoreExpr)
     <+ promoteT (ppCoreProg :: PrettyH CoreProg)
     <+ promoteT (ppCoreBind :: PrettyH GHC.CoreBind)
     <+ promoteT (ppCoreDef  :: PrettyH CoreDef)
     <+ promoteT (ppModGuts  :: PrettyH GHC.ModGuts)
     <+ promoteT (ppCoreAlt  :: PrettyH GHC.CoreAlt)

------------------------------------------------------------------------------------------------
