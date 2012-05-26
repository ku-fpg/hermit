{-# LANGUAGE FlexibleInstances #-}

module Language.HERMIT.PrettyPrinter where

import GhcPlugins hiding ((<>))

import Text.PrettyPrint.MarkedHughesPJ as PP
import Language.HERMIT.HermitKure
import Control.Applicative
import Data.Default

import Language.KURE


-- A HERMIT document
type DocH = MDoc HermitMark

-- These are the zero-width marks on the document
data HermitMark
        = PushAttr Attr
        | PopAttr
    deriving Show

-- These are the attributes
data Attr = PathAttr [Int]
          | Color SyntaxForColor
    deriving Show

data SyntaxForColor             -- (suggestion)
        = KeywordColor          -- bold
        | SyntaxColor
        | VarColor
    deriving Show

attr :: Attr -> DocH -> DocH
attr a p = mark (PushAttr a) <> p <> mark PopAttr

varColor :: DocH -> DocH
varColor = attr (Color VarColor)

keywordColor :: DocH -> DocH
keywordColor = attr (Color KeywordColor)

type PrettyH a = TranslateH a DocH

-- These are *recommendations* to the pretty printer.

data PrettyOptions = PrettyOptions
        { po_fullyQualified  :: Bool            -- Do you show fully qualified names?
        , po_hideTypes       :: Bool            -- Do you hide types, and type arguments, as <>?
        , po_typesForBinders :: Bool            -- Do you give the types for all bindings?
        , po_highlight       :: Maybe Path      -- This region should be highlighted (for sub-expression)
        , po_depth           :: Maybe Int       -- below this depth are ..., Nothing => infinite
        , po_notes           :: Bool            -- ^ notes might be added to output
        } deriving Show

instance Default PrettyOptions where
  def = PrettyOptions
        { po_fullyQualified  = False
        , po_hideTypes       = True
        , po_typesForBinders = True
        , po_highlight       = Nothing
        , po_depth           = Nothing
        , po_notes           = False
        }

-- Other options for pretty printing:
-- * Does a top level program should function names, or complete listings?

-- This is the hacky old pretty printer, using the new API
ghcCorePrettyH :: PrettyH Core
ghcCorePrettyH =
           promoteT (ppModule :: PrettyH ModGuts)
        <+ promoteT (ppH      :: PrettyH CoreProgram)
        <+ promoteT (ppH      :: PrettyH CoreBind)
        <+ promoteT (ppDef    :: PrettyH CoreDef)
        <+ promoteT (ppH      :: PrettyH CoreExpr)
        <+ promoteT (ppH      :: PrettyH CoreAlt)
  where

        ppH :: (Outputable a) => PrettyH a
        ppH = liftT (PP.text . showSDoc . ppr)

        ppModule :: PrettyH ModGuts
        ppModule = liftT mg_module >-> ppH

        ppDef :: PrettyH CoreDef
        ppDef = liftT (\ (Def v e) -> (v,e)) >-> ppH

--        liftT (PP.text . ppr . mg_module)

-- Later, this will have depth, and other pretty print options.
class Show2 a where
        show2 :: a -> String

instance Show2 Core where
        show2 (ModGutsCore   m)  = show2 m
        show2 (ProgramCore   p)  = show2 p
        show2 (BindCore      bd) = show2 bd
        show2 (ExprCore      e)  = show2 e
        show2 (AltCore       a)  = show2 a
        show2 (DefCore       a)  = show2 a

instance Show2 ModGuts where
        show2 modGuts =
                "[ModGuts for " ++ showSDoc (ppr (mg_module modGuts)) ++ "]\n" ++
                 show (length (mg_binds modGuts)) ++ " binding group(s)\n" ++
                 show (length (mg_rules modGuts)) ++ " rule(s)\n" ++
                 showSDoc (ppr (mg_rules modGuts))


instance Show2 CoreProgram where
        show2 codeProg =
                "[Code Program]\n" ++
                showSDoc (ppr codeProg)

instance Show2 CoreExpr where
        show2 expr =
                "[Expr]\n" ++
                showSDoc (ppr expr)

instance Show2 CoreAlt where
        show2 alt =
                "[alt]\n" ++
                showSDoc (ppr alt)


instance Show2 CoreBind where
        show2 bind =
                "[Bind]\n" ++
                showSDoc (ppr bind)

instance Show2 CoreDef where
        show2 (Def v e) =
                "[Def]\n" ++
                showSDoc (ppr v) ++ " = " ++ showSDoc (ppr e)


