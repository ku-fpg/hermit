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
        | RetApp DocH [DocH]    -- the arguments are pre-paren'd if needed
        | RetExpr DocH
        | RetAtom DocH         -- parens not needed


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
normalExpr (RetApp fn xs) = sep ( fn : map (nest 2) xs )
normalExpr (RetExpr e0)    = e0
normalExpr (RetAtom e0)    = e0

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
            isInfix = all (\ n -> n `elem` "!@#$%^&*-_+=:?/\\<>'")


    -- binders are vars that is bound by lambda or case, etc.
    ppBinder :: GHC.Var -> DocH
    ppBinder var
            | GHC.isTyVar var = typeBindSymbol
            | otherwise   = ppVar var

    -- Use for any GHC structure, the 'showSDoc' prefix is to remind us
    -- that we are eliding infomation here.
    ppSDoc :: (GHC.Outputable a) => a -> MDoc b
    ppSDoc = toDoc . (if hideNotes then id else ("showSDoc: " ++)) . GHC.showSDoc . GHC.ppr
        where toDoc s | any isSpace s = parens (text s)
                      | otherwise     = text s

    ppModGuts :: PrettyH GHC.ModGuts
    ppModGuts =   arr $ \ m -> hang (keyword "module" <+> ppSDoc (GHC.mg_module m) <+> keyword "where") 2
                               (vcat [ ppBinder v
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

    ppCoreExprR :: TranslateH GHC.CoreExpr RetExpr
    ppCoreExprR = lamT ppCoreExprR (\ v e -> case e of
                                              RetLam vs e0  -> RetLam (ppBinder v : vs) e0
                                              _             -> RetLam [ppBinder v] (normalExpr e))
               <+ letT ppCoreBind ppCoreExprR
                                   (\ bd e -> case e of
                                              RetLet vs e0  -> RetLet (bd : vs) e0
                                              _             -> RetLet [bd] (normalExpr e))
               <+ appT ppCoreExprR ppCoreExprR
                                   (\ e1 e2 -> case e1 of
                                              RetApp f xs   -> RetApp f (xs ++ [atomExpr e2])
                                              _             -> RetApp (atomExpr e1) [atomExpr e2])
               <+ varT (\ i -> RetAtom (ppVar i))
               <+ litT (\ i -> RetAtom (ppSDoc i))
               <+ typeT (\ _ -> RetAtom typeSymbol)
               <+ (ppCoreExpr0 >>^ RetExpr)

    ppCoreExpr0 :: PrettyH GHC.CoreExpr
    ppCoreExpr0 = caseT ppCoreExpr (const ppCoreAlt) (\ s b ty alts ->
                        (keywordColor (text "case") <+> s <+> keywordColor (text "of") <+> ppBinder b) $$
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
                           | otherwise = hsep (map ppBinder ids) <+> specialSymbol RightArrowSymbol

    -- GHC uses a tuple, which we print here. The CoreDef type is our doing.
    ppCoreDef :: PrettyH CoreDef
    ppCoreDef = defT ppCoreExprR ppDefFun

    ppDefFun :: GHC.Id -> RetExpr -> DocH
    ppDefFun i e = case e of
                    RetLam vs e0 -> hang (pre <+> specialSymbol LambdaSymbol <+> hsep vs <+> specialSymbol RightArrowSymbol) 2 e0
                    _ -> hang pre 2 (normalExpr e)
        where
            pre = ppBinder i <+> symbol '='
