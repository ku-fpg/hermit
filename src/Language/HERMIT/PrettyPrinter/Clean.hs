{-# LANGUAGE CPP, LambdaCase #-}

module Language.HERMIT.PrettyPrinter.Clean
  ( -- * HERMIT's Clean Pretty-Printer for GHC Core
    corePrettyH
  )
where

import Control.Monad (ap)
import Control.Arrow hiding ((<+>))

import Data.Char (isSpace)
import Data.List (partition)
import Data.Traversable (sequenceA)


import qualified GhcPlugins as GHC

import Language.HERMIT.Syntax
import Language.HERMIT.Kure
import Language.HERMIT.Core
import Language.HERMIT.PrettyPrinter.Common
import Language.HERMIT.GHC

import TypeRep (TyLit(..))
import Pair

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
ppParens p = symbol '(' <> p <> symbol ')'

normalExprWithParens :: RetExpr -> DocH
normalExprWithParens (RetAtom e)   = e
normalExprWithParens RetEmpty      = empty
normalExprWithParens (RetApp d []) = d
normalExprWithParens other         = ppParens (normalExpr other)

normalExprWithParensExceptApp :: RetExpr -> DocH
normalExprWithParensExceptApp e@(RetApp _ _) = normalExpr e
normalExprWithParensExceptApp e              = normalExprWithParens e

normalExpr :: RetExpr -> DocH
normalExpr (RetLam vs e)  = hang (specialSymbol LambdaSymbol <+> hsep vs <+> specialSymbol RightArrowSymbol) 2 e
normalExpr (RetLet vs e)  = sep [ keyword "let" <+> vcat vs, keyword "in" <+> e ]
normalExpr (RetApp fn xs) = let (xs1,xs2) = partition isAtom xs
                             in sep [ hsep (fn : map normalExpr xs1)
                                    , nest 2 (sep $ map normalExprWithParens xs2) ]
normalExpr (RetExpr e)    = e
normalExpr (RetAtom e)    = e
normalExpr (RetEmpty)     = empty

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

coText :: String -> DocH
coText = coercionColor . text

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

tyText :: String -> DocH
tyText = typeColor . text

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

        ppTyCon :: GHC.TyCon -> DocH
        ppTyCon = ppName TypeColor . GHC.getName

        ppTyConCo :: GHC.TyCon -> DocH
        ppTyConCo = ppName CoercionColor . GHC.getName

        ppTypeMode :: GHC.Type -> RetExpr
        ppTypeMode t = case po_exprTypes opts of
                         Omit     -> RetEmpty
                         Abstract -> RetAtom typeSymbol
                         _        -> ppCoreType t

        ppCoercionMode :: GHC.Coercion -> RetExpr
        ppCoercionMode co = case po_coercions opts of
                              Omit     -> RetEmpty
                              Abstract -> RetAtom coercionSymbol
                              Show     -> ppCoreCoercion co
                              Kind     -> RetExpr (coercionSymbol <+> specialSymbol TypeOfSymbol <+> ppCoKind co)

        -- binders are vars that is bound by lambda or case, etc.
        ppBinder :: GHC.Var -> Maybe DocH
        ppBinder var | GHC.isTyVar var = case po_exprTypes opts of
                                           Omit     -> Nothing
                                           Abstract -> Just typeBindSymbol
                                           _        -> Just (ppVar var)
                     | GHC.isCoVar var = case po_coercions opts of
                                           Omit     -> Nothing
                                           Abstract -> Just coercionBindSymbol
                                           Show     -> Just (ppVar var)
                                           Kind     -> Just $ ppParens (coercionBindSymbol <+> specialSymbol TypeOfSymbol <+> ppCoKind (GHC.CoVarCo var))
                                                       -- TODO: refactor this to be more systematic.  It should be possible to request type sigs for all type bindings.
                     | otherwise       = Just $ ppVar var

        -- Use for any GHC structure, the 'showSDoc' prefix is to remind us
        -- that we are eliding infomation here.
        ppSDoc :: GHC.Outputable a => a -> MDoc b
        ppSDoc = toDoc . (if hideNotes then id else ("showSDoc: " ++)) . GHC.showSDoc dynFlags . GHC.ppr
            where toDoc s | any isSpace s = parens (text s)
                          | otherwise     = text s

        ppModGuts :: PrettyH GHC.ModGuts
        ppModGuts =   arr $ \ m -> hang (keyword "module" <+> ppSDoc (GHC.mg_module m) <+> keyword "where") 2
                                   (vcat [ (optional (ppBinder v) (\b -> b <+> specialSymbol TypeOfSymbol <+> normalExpr (ppCoreType $ GHC.idType v)))
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

        ppApp :: RetExpr -> RetExpr -> RetExpr
        ppApp e1 e2 = case e1 of
                        RetApp f xs   -> RetApp f (snocNonEmpty xs e2)
                        _             -> case e2 of -- if there are no (displayed) args then don't parenthesise
                                           RetEmpty -> e1
                                           args     -> RetApp (normalExprWithParens e1) (snocNonEmpty [] args)

        snocNonEmpty :: [RetExpr] -> RetExpr -> [RetExpr]
        snocNonEmpty xs RetEmpty = xs
        snocNonEmpty xs e        = xs ++ [e]

        ppCoreExprR :: TranslateH GHC.CoreExpr RetExpr
        ppCoreExprR = ppCoreExprPR `ap` rootPathT

        ppCoreExprPR :: TranslateH GHC.CoreExpr (Path -> RetExpr)
        ppCoreExprPR = lamT ppCoreExprR (\ v e _ -> case e of
                                                  RetLam vs e0  -> RetLam (consMaybe (ppBinder v) vs) e0
                                                  _             -> RetLam (consMaybe (ppBinder v) []) (normalExpr e))

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

                   <+ appT ppCoreExprR ppCoreExprR (\ e1 e2 _ -> ppApp e1 e2)

                   <+ caseT ppCoreExpr (const ppCoreAlt) (\ s b _ alts p -> RetExpr $ attrP p ((keyword "case" <+> s <+> keyword "of" <+> optional (ppBinder b) id) $$ nest 2 (vcat alts)))
                   <+ varT (\ i p -> RetAtom (attrP p $ ppVar i))
                   <+ litT (\ i p -> RetAtom (attrP p $ ppSDoc i))
                   <+ typeT (\ t p -> attrPAtomExpr p $ ppTypeMode t)
                   <+ coercionT (\ co p -> attrPAtomExpr p $ ppCoercionMode co)
                   <+ castT ppCoreExprR (\ e co p -> let e' = normalExprWithParensExceptApp e
                                                      in case ppCoercionMode co of
                                                           RetEmpty    -> e
                                                           RetAtom pCo -> RetExpr $ attrP p (e' <+> castSymbol <+> pCo)
                                                           pCo         -> RetExpr $ attrP p (e' <+> castSymbol <+> normalExprWithParensExceptApp pCo)
                                                     )
                   <+ tickT ppCoreExpr (\ i e p -> RetExpr $ attrP p (text "Tick" $$ nest 2 (ppSDoc i <+> parens e)))

        attrPAtomExpr :: Path -> RetExpr -> RetExpr
        attrPAtomExpr p (RetAtom d) = RetAtom (attrP p d)
        attrPAtomExpr p (RetExpr d) = RetExpr (attrP p d)
        attrPAtomExpr _ e           = e

        ppCoreType :: GHC.Type -> RetExpr
        ppCoreType (TyVarTy v)   = RetAtom (ppVar v)
        ppCoreType (LitTy tylit) = RetAtom (ppLitTy tylit)
        ppCoreType (AppTy t1 t2) = let e1 = ppCoreType t1
                                       e2 = ppCoreType t2
                                    in ppApp e1 e2
        ppCoreType (FunTy ty1 ty2) = RetExpr $ normalExprWithParensExceptApp (ppCoreType ty1) <+> typeArrow <+> normalExpr (ppCoreType ty2)
        ppCoreType (ForAllTy v ty) = RetExpr $ specialSymbol ForallSymbol <+> ppVar v <+> symbol '.' <+> normalExpr (ppCoreType ty)
        ppCoreType (TyConApp tyCon tys)
                    | GHC.isFunTyCon tyCon, [ty1,ty2] <- tys = ppCoreType (FunTy ty1 ty2)
                    | tyCon == GHC.listTyCon = RetAtom $ tyText "[" <> (case map (normalExpr . ppCoreType) tys of
                                                                            []  -> empty
                                                                            t:_ -> t                     ) <> tyText "]"
                    | GHC.isTupleTyCon tyCon = case map (normalExpr . ppCoreType) tys of
                                                [] -> RetAtom $ tyText "()"
                                                ds -> RetAtom $ tyText "(" <> (foldr1 (\d r -> d <> tyText "," <+> r) ds) <> tyText ")"
                    | otherwise              = RetApp (ppTyCon tyCon) (map ppCoreType tys)

        ppCoreCoercion :: GHC.Coercion -> RetExpr
        ppCoreCoercion (GHC.Refl t)            = let refl = coKeyword "refl"
                                                  in case po_exprTypes opts of
                                                       Omit -> RetAtom refl
                                                       _    -> RetExpr (refl <+> normalExprWithParens (ppTypeMode t))
        ppCoreCoercion (GHC.CoVarCo v)         = RetAtom (ppVar v)
        ppCoreCoercion (GHC.SymCo co)          = RetExpr (coKeyword "sym" <+> normalExprWithParens (ppCoreCoercion co))
        ppCoreCoercion (GHC.ForAllCo v co)     = let e = ppCoreCoercion co
                                                  in case po_exprTypes opts of
                                                       Omit -> e
                                                       _    -> RetExpr (specialSymbol ForallSymbol <+> optional (ppBinder v) (\d -> d <+> symbol '.' <+> normalExprWithParensExceptApp e))
        ppCoreCoercion (GHC.TransCo co1 co2)   = RetExpr (normalExprWithParensExceptApp (ppCoreCoercion co1) <+> coChar ';' <+> normalExprWithParensExceptApp (ppCoreCoercion co2))
        ppCoreCoercion (GHC.UnsafeCo t1 t2)    = RetExpr (ppTypePairCoercion t1 t2)
        ppCoreCoercion (GHC.NthCo n co)        = RetExpr (coKeyword "nth" <+> coText (show n) <+> normalExprWithParens (ppCoreCoercion co))
        ppCoreCoercion (GHC.InstCo co t)       = let e = ppCoreCoercion co
                                                  in case po_exprTypes opts of
                                                       Omit -> e
                                                       _    -> RetExpr (normalExprWithParensExceptApp e <+> coChar '@' <+> normalExprWithParensExceptApp (ppTypeMode t))
        ppCoreCoercion (GHC.TyConAppCo tc cs)  = RetApp (ppTyConCo tc) (map ppCoreCoercion cs)
        ppCoreCoercion (GHC.AppCo co1 co2)     = let e1 = ppCoreCoercion co1
                                                     e2 = ppCoreCoercion co2
                                                  in ppApp e1 e2
#if __GLASGOW_HASKELL__ > 706
        -- TODO: Figure out how to properly pp new branched Axioms and Left/Right Coercions
        ppCoreCoercion (GHC.AxiomInstCo ax idx cs) = RetApp (coercionColor $ ppSDoc ax) (RetAtom (ppSDoc idx) : map ppCoreCoercion cs)
        ppCoreCoercion (GHC.LRCo lr co) = RetApp (coercionColor $ ppSDoc lr) [ppCoreCoercion co]
#else
        ppCoreCoercion (GHC.AxiomInstCo ax cs) = RetApp (coercionColor $ ppSDoc ax) (map ppCoreCoercion cs) -- TODO: add pretty printer for Coercion Axioms
#endif

        ppTypePairCoercion :: Type -> Type -> DocH
        ppTypePairCoercion t1 t2 = normalExprWithParensExceptApp (ppTypeMode t1) <+> coChar '~' <+> normalExprWithParensExceptApp (ppTypeMode t2)

        ppCoKind :: GHC.Coercion -> DocH
        ppCoKind = uncurry ppTypePairCoercion . unPair . GHC.coercionKind

        ppCoreTypeSig :: PrettyH GHC.CoreExpr
        ppCoreTypeSig = arr (\case
                                GHC.Coercion c -> ppCoKind c
                                e              -> normalExpr $ ppCoreType $ GHC.exprType e)

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
                              Show     -> if GHC.isCoVar v
                                           then let coTySig = specialSymbol TypeOfSymbol <+> ty
                                                 in case po_coercions opts of
                                                      Omit     -> empty
                                                      Show     -> (ppVar v <+> coTySig) $+$ body
                                                      _        -> (coercionBindSymbol <+> coTySig)
                                           else (ppVar v <+> specialSymbol TypeOfSymbol <+> ty) $+$ body
                              Omit     -> if GHC.isTyVar v
                                           then empty
                                           else body
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

consMaybe :: Maybe a -> [a] -> [a]
consMaybe Nothing  as = as
consMaybe (Just a) as = a : as

------------------------------------------------------------------------------------------------
