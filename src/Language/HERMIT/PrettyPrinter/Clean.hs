-- | Output the raw Expr constructors. Helpful for writing pattern matching rewrites.
module Language.HERMIT.PrettyPrinter.Clean where

import Control.Arrow hiding ((<+>))

import Data.Char (isSpace)
import Data.Traversable (sequenceA)

import qualified GhcPlugins as GHC
import Language.HERMIT.HermitKure
import Language.HERMIT.PrettyPrinter
import Language.KURE
import Language.KURE.Injection
import Language.HERMIT.GHC

import Text.PrettyPrint.MarkedHughesPJ as PP

listify :: (MDoc a -> MDoc a -> MDoc a) -> [MDoc a] -> MDoc a
listify _  []     = text "[]"
listify op (d:ds) = op (text "[ " <> d) (foldr (\e es -> op (text ", " <> e) es) (text "]") ds)

-- | like vcat and hcat, only make the list syntax explicit
vlist, hlist :: [MDoc a] -> MDoc a
vlist = listify ($$)
hlist = listify (<+>)

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
normalExpr (RetLet vs e0) = sep [ keywordColor (text "let") <+> vcat vs, keywordColor (text "in") <+> e0 ]
normalExpr (RetApp fn xs) = sep [ hsep (fn : map atomExpr (takeWhile isAtom xs))
                                , nest 2 (sep (map atomExpr (dropWhile isAtom xs))) ]
normalExpr (RetExpr e0)    = e0
normalExpr (RetAtom e0)    = e0
normalExpr (RetEmpty)      = empty

typeSymbol :: DocH
typeSymbol = markColor TypeColor (specialFont $ char $ renderSpecial TypeSymbol)

typeBindSymbol :: DocH
typeBindSymbol = markColor TypeColor (specialFont $ char $ renderSpecial TypeBindSymbol)

corePrettyH :: PrettyOptions -> PrettyH Core
corePrettyH opts =
       promoteT (ppCoreExpr :: PrettyH GHC.CoreExpr)
    <+ promoteT (ppProgram  :: PrettyH GHC.CoreProgram)
    <+ promoteT (ppCoreBind :: PrettyH GHC.CoreBind)
    <+ promoteT (ppCoreDef  :: PrettyH CoreDef)
    <+ promoteT (ppModGuts  :: PrettyH GHC.ModGuts)
    <+ promoteT (ppCoreAlt  :: PrettyH GHC.CoreAlt)
  where
    hideNotes = True
    -- Only use for base types!
    ppShow :: (Show a) => a -> MDoc b
    ppShow = text . show

    ppVar :: GHC.Var -> DocH
    ppVar = ppName . GHC.varName

    ppName :: GHC.Name -> DocH
    ppName nm
            | isInfix name = ppParens $ varColor $ text name
            | otherwise    = varColor $ text name
      where name = GHC.occNameString $ GHC.nameOccName $ nm
            isInfix = all (\ n -> n `elem` "!@#$%^&*-._+=:?/\\<>'")


    -- binders are vars that is bound by lambda or case, etc.
    ppBinder :: GHC.Var -> Maybe DocH
    ppBinder var = case po_exprTypes opts of
                    Abstract | GHC.isTyVar var -> Just $ typeBindSymbol
                    Omit     | GHC.isTyVar var -> Nothing
                    _                          -> Just $ ppVar var

    ppIdBinder :: GHC.Id -> DocH
    ppIdBinder var = ppVar var

    -- Use for any GHC structure, the 'showSDoc' prefix is to remind us
    -- that we are eliding infomation here.
    ppSDoc :: (GHC.Outputable a) => a -> MDoc b
    ppSDoc = toDoc . (if hideNotes then id else ("showSDoc: " ++)) . GHC.showSDoc . GHC.ppr
        where toDoc s | any isSpace s = parens (text s)
                      | otherwise     = text s

    ppModGuts :: PrettyH GHC.ModGuts
    ppModGuts =   arr $ \ m -> hang (keyword "module" <+> ppSDoc (GHC.mg_module m) <+> keyword "where") 2
                               (vcat [ (ppIdBinder v <+> specialSymbol TypeOfSymbol <+> ppCoreType (GHC.idType v))
                                     | bnd <- GHC.mg_binds m
                                     , v <- case bnd of
                                              GHC.NonRec f _ -> [f]
                                              GHC.Rec bnds -> map fst bnds
                                   ])

    -- DocH is not a monoid, so we can't use listT here
    ppProgram :: PrettyH GHC.CoreProgram -- CoreProgram = [CoreBind]
    ppProgram = translate $ \ c -> fmap vcat . sequenceA . map (apply ppCoreBind c)

    ppCoreExpr :: PrettyH GHC.CoreExpr
    ppCoreExpr = ppCoreExprR >>^ normalExpr

    appendArg xs (RetEmpty) = xs
    appendArg xs e          = xs ++ [e]

    appendBind Nothing  xs = xs
    appendBind (Just v) xs = v : xs

    ppCoreExprR :: TranslateH GHC.CoreExpr RetExpr
    ppCoreExprR = lamT ppCoreExprR (\ v e -> case e of
                                              RetLam vs e0  -> RetLam (appendBind (ppBinder v) vs) e0
                                              _             -> RetLam (appendBind (ppBinder v) []) (normalExpr e))
               <+ letT ppCoreBind ppCoreExprR
                                   (\ bd e -> case e of
                                              RetLet vs e0  -> RetLet (bd : vs) e0
                                              _             -> RetLet [bd] (normalExpr e))
               -- HACK!
               <+ (acceptR (\ e -> case e of
                                     GHC.App (GHC.Var v) (GHC.Type t) | po_exprTypes opts == Abstract -> True
                                     _ -> False) >>>
                           (appT ppCoreExprR ppCoreExprR (\ (RetAtom e1) (RetAtom e2) ->
                                    RetAtom (e1 <+> e2))))
               <+ appT ppCoreExprR ppCoreExprR
                                   (\ e1 e2 -> case e1 of
                                              RetApp f xs   -> RetApp f (appendArg xs e2)
                                              _             -> case e2 of -- if our only args are types, and they are omitted, don't paren
                                                                RetEmpty -> e1
                                                                args -> RetApp (atomExpr e1) (appendArg [] args))
               <+ varT (\ i -> RetAtom (ppVar i))
               <+ litT (\ i -> RetAtom (ppSDoc i))
               <+ typeT (\ t -> case po_exprTypes opts of
                                  Show     -> RetAtom (ppCoreType t)
                                  Abstract -> RetAtom typeSymbol
                                  Omit     -> RetEmpty)
               <+ (ppCoreExpr0 >>^ RetExpr)

    ppCoreType :: GHC.Type -> DocH
    ppCoreType (TyVarTy v)   = ppVar v
    ppCoreType (AppTy t1 t2) = ppParens (ppCoreType t1 <+> ppCoreType t2)
    ppCoreType (TyConApp tyCon tys)
        | GHC.isFunTyCon tyCon, [ty1,ty2] <- tys = ppCoreType (FunTy ty1 ty2)
        | otherwise = ppName (GHC.getName tyCon) <+> sep (map ppCoreType tys)
    ppCoreType (FunTy ty1 ty2) = ppCoreType ty1 <+> text "->" <+> ppCoreType ty2
    ppCoreType (ForAllTy v ty) = specialSymbol ForallSymbol <+> ppVar v <+> symbol '.' <+> ppCoreType ty

    ppCoreExpr0 :: PrettyH GHC.CoreExpr
    ppCoreExpr0 = caseT ppCoreExpr (const ppCoreAlt) (\ s b ty alts ->
                        (keywordColor (text "case") <+> s <+> keywordColor (text "of") <+> ppIdBinder b) $$
                          nest 2 (vcat alts))
              <+ castT ppCoreExpr (\e co -> text "Cast" $$ nest 2 ((parens e) <+> ppSDoc co))
              <+ tickT ppCoreExpr (\i e  -> text "Tick" $$ nest 2 (ppSDoc i <+> parens e))
--              <+ typeT (\ty -> text "Type" <+> nest 2 (ppSDoc ty))
              <+ coercionT (\co -> text "Coercion" $$ nest 2 (ppSDoc co))

    ppCoreBind :: PrettyH GHC.CoreBind
    ppCoreBind = nonRecT ppCoreExprR ppDefFun
              <+ recT (const ppCoreDef) (\ bnds -> keywordColor (text "rec") <+> vcat bnds)

    ppCoreAlt :: PrettyH GHC.CoreAlt
    ppCoreAlt = altT ppCoreExpr $ \ con ids e -> case con of
                  GHC.DataAlt dcon -> hang (ppName (GHC.dataConName dcon) <+> ppIds ids) 2 e
                  GHC.LitAlt lit   -> hang (ppSDoc lit <+> ppIds ids) 2 e
                  GHC.DEFAULT      -> symbol '_' <+> ppIds ids <+> e
          where
                 ppIds ids | null ids  = specialSymbol RightArrowSymbol
                           | otherwise = hsep (map ppIdBinder ids) <+> specialSymbol RightArrowSymbol

    -- GHC uses a tuple, which we print here. The CoreDef type is our doing.
    ppCoreDef :: PrettyH CoreDef
    ppCoreDef = defT ppCoreExprR ppDefFun

    ppDefFun :: GHC.Id -> RetExpr -> DocH
    ppDefFun i e = case e of
                    RetLam vs e0 -> hang (pre <+> specialSymbol LambdaSymbol <+> hsep vs <+> specialSymbol RightArrowSymbol) 2 e0
                    _ -> hang pre 2 (normalExpr e)
        where
            pre = case ppBinder i of
                    Nothing -> empty
                    Just p  -> p <+> symbol '='
