-- | Output the raw Expr constructors. Helpful for writing pattern matching rewrites.
module Language.HERMIT.PrettyPrinter.Clean where

import Data.Char (isSpace)
import Data.Traversable (sequenceA)

import qualified GhcPlugins as GHC
import Language.HERMIT.HermitKure
import Language.HERMIT.PrettyPrinter
import Language.KURE

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


atomExpr :: RetExpr -> DocH
atomExpr (RetAtom e) = e
atomExpr other       = parens (normalExpr other)

normalExpr :: RetExpr -> DocH
normalExpr (RetLam vs e0) = hang (text "\x03BB" <+> hsep vs <+> text "\x2192") 2 e0
normalExpr (RetLet vs e0) = sep [ keywordColor (text "let") <+> vcat vs, keywordColor (text "in") <+> e0 ]
normalExpr (RetApp fn xs) = sep ( fn : map (nest 2) xs )
normalExpr (RetExpr e0)    = e0
normalExpr (RetAtom e0)    = e0


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
    ppVar = varColor . text . GHC.occNameString . GHC.nameOccName . GHC.varName

    -- binders are vars that is bound by lambda or case, etc.
    ppBinder :: GHC.Var -> DocH
    ppBinder = ppVar

    -- Use for any GHC structure, the 'showSDoc' prefix is to remind us
    -- that we are eliding infomation here.
    ppSDoc :: (GHC.Outputable a) => a -> MDoc b
    ppSDoc = toDoc . (if hideNotes then id else ("showSDoc: " ++)) . GHC.showSDoc . GHC.ppr
        where toDoc s | any isSpace s = parens (text s)
                      | otherwise     = text s

    ppModGuts :: PrettyH GHC.ModGuts
    ppModGuts = liftT (ppSDoc . GHC.mg_module)

    -- DocH is not a monoid, so we can't use listT here
    ppProgram :: PrettyH GHC.CoreProgram -- CoreProgram = [CoreBind]
    ppProgram = translate $ \ c -> fmap vcat . sequenceA . map (apply ppCoreBind c)

    ppCoreExpr :: PrettyH GHC.CoreExpr
    ppCoreExpr = ppCoreExprR >-> liftT normalExpr

    ppCoreExprR :: TranslateH GHC.CoreExpr RetExpr
    ppCoreExprR = lamT ppCoreExprR (\ v e -> case e of
                                              RetLam vs e0  -> RetLam (ppVar (v) : vs) e0
                                              _             -> RetLam [ppVar (v)] (normalExpr e))
               <+ letT ppCoreBind ppCoreExprR
                                   (\ bd e -> case e of
                                              RetLet vs e0  -> RetLet (bd : vs) e0
                                              _             -> RetLet [bd] (normalExpr e))
               <+ appT ppCoreExprR ppCoreExprR
                                   (\ e1 e2 -> case e1 of
                                              RetApp f xs   -> RetApp f (xs ++ [atomExpr e2])
                                              _             -> RetApp (atomExpr e1) [atomExpr e2])
               <+ (ppCoreAtom0 >-> liftT RetAtom)
               <+ (ppCoreExpr0 >-> liftT RetExpr)

    ppCoreAtom0 :: PrettyH GHC.CoreExpr
    ppCoreAtom0 = varT (\i -> ppVar (i))
              <+ litT (\i -> ppSDoc i)
              <+ typeT (\ _ -> text "\x25B5") -- "\x221E") -- "\x25c6")

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
              <+ recT (const ppCoreDef) (\ bnds -> keywordColor (text "\x03BC") <+> vcat bnds)

    ppCoreAlt :: PrettyH GHC.CoreAlt
    ppCoreAlt = altT ppCoreExpr $ \ con ids e -> case con of
                  GHC.DataAlt dcon -> hang (ppSDoc dcon <+> ppIds ids) 2 e
                  GHC.LitAlt lit   -> hang (ppSDoc lit <+> ppIds ids) 2 e
                  GHC.DEFAULT      -> text "_" <+> ppIds ids <+> e
          where
                 ppIds ids | null ids  = text "\x2192"
                           | otherwise = hsep (map ppBinder ids) <+> text "\x2192"

    -- GHC uses a tuple, which we print here. The CoreDef type is our doing.
    ppCoreDef :: PrettyH CoreDef
    ppCoreDef = defT ppCoreExprR ppDefFun

    ppDefFun :: GHC.Id -> RetExpr -> DocH
    ppDefFun i e = case e of
                    RetLam vs e0 -> hang (pre <+> text "\x03BB" <+> hsep vs <+> text "\x2192") 2 e0
                    _ -> hang pre 2 (normalExpr e)
        where
            pre = ppBinder i <+> text "="
