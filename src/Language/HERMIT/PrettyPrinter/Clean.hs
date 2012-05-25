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


argExpr :: RetExpr -> DocH
argExpr (RetAtom e) = e
argExpr other       = parens (normalExpr other)

normalExpr :: RetExpr -> DocH
normalExpr (RetLam vs e0) = hang (text "\x03BB" <+> hsep vs <+> text "\x2192") 2 e0
normalExpr (RetLet vs e0) = sep [ text "let" <+> vcat vs, text "in" <+> e0 ]
normalExpr (RetApp fn xs) = fn <+> sep xs
normalExpr (RetExpr e0)    = e0
normalExpr (RetAtom e0)    = e0


corePrettyH :: PrettyH Core
corePrettyH  =
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
    ppProgram = translate $ \ c -> fmap vlist . sequenceA . map (apply ppCoreBind c)

    ppCoreExpr :: PrettyH GHC.CoreExpr
    ppCoreExpr = ppCoreExprR >-> liftT normalExpr

    ppCoreExprR :: TranslateH GHC.CoreExpr RetExpr
    ppCoreExprR = lamT ppCoreExprR (\ v e -> case e of
                                              RetLam vs e0  -> RetLam (varColor (ppSDoc v) : vs) e0
                                              _             -> RetLam [varColor (ppSDoc v)] (normalExpr e))
               <+ letT ppCoreBind ppCoreExprR
                                   (\ bd e -> case e of
                                              RetLet vs e0  -> RetLet (bd : vs) e0
                                              _             -> RetLet [bd] (normalExpr e))
               <+ appT ppCoreExprR ppCoreExprR
                                   (\ e1 e2 -> case e1 of
                                              RetApp f xs   -> RetApp f (xs ++ [argExpr e2])
                                              _             -> RetApp (normalExpr e1) [argExpr e2])
               <+ (ppCoreAtom0 >-> liftT RetAtom)
               <+ (ppCoreExpr0 >-> liftT RetExpr)

    ppCoreAtom0 :: PrettyH GHC.CoreExpr
    ppCoreAtom0 = varT (\i -> varColor (ppSDoc i))
              <+ litT (\i -> ppSDoc i)
              <+ typeT (\ _ -> text "\x25c6")

    ppCoreExpr0 :: PrettyH GHC.CoreExpr
    ppCoreExpr0 = caseT ppCoreExpr (const ppCoreAlt) (\s b ty alts ->
                        text "Case" $$ nest 2 (parens s)
                                    $$ nest 2 (ppSDoc b)
                                    $$ nest 2 (ppSDoc ty)
                                    $$ nest 2 (vlist alts))
              <+ castT ppCoreExpr (\e co -> text "Cast" $$ nest 2 ((parens e) <+> ppSDoc co))
              <+ tickT ppCoreExpr (\i e  -> text "Tick" $$ nest 2 (ppSDoc i <+> parens e))
--              <+ typeT (\ty -> text "Type" <+> nest 2 (ppSDoc ty))
              <+ coercionT (\co -> text "Coercion" $$ nest 2 (ppSDoc co))

    ppCoreBind :: PrettyH GHC.CoreBind
    ppCoreBind = nonRecT ppCoreExpr (\i e -> ppSDoc i <+> text "=" <+> e)
              <+ recT (const ppCoreDef) (\ bnds -> text "\x03BC" <+> vcat bnds)

    ppCoreAlt :: PrettyH GHC.CoreAlt
    ppCoreAlt = altT ppCoreExpr $ \ con ids e -> text "Alt" <+> ppSDoc con
                                                            <+> (hlist $ map ppSDoc ids)
                                                            $$ nest 2 (parens e)

    -- GHC uses a tuple, which we print here. The CoreDef type is our doing.
    ppCoreDef :: PrettyH CoreDef
    ppCoreDef = defT ppCoreExpr $ \ i e -> varColor (ppSDoc i) <+> text "=" <+> e
