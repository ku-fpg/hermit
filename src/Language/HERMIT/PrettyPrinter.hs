{-# LANGUAGE FlexibleInstances #-}

module Language.HERMIT.PrettyPrinter where

import GhcPlugins hiding ((<>))

import Text.PrettyPrint.MarkedHughesPJ as PP
import Language.HERMIT.Kure
import Control.Arrow
import Data.Monoid hiding ((<>))
import Data.Default
import Data.Char
import qualified Data.Map as M
import System.IO


-- A HERMIT document
type DocH = MDoc HermitMark

-- These are the zero-width marks on the document
data HermitMark
        = PushAttr Attr
        | PopAttr
    deriving Show

-- These are the attributes
data Attr = PathAttr Path
          | Color SyntaxForColor
          | SpecialFont
    deriving Show

data SyntaxForColor             -- (suggestion)
        = KeywordColor          -- bold
        | SyntaxColor
        | VarColor
        | TypeColor
        | LitColor
    deriving Show

attr :: Attr -> DocH -> DocH
attr a p = mark (PushAttr a) <> p <> mark PopAttr

attrP :: Path -> DocH -> DocH
attrP = attr . PathAttr

varColor :: DocH -> DocH
varColor = attr (Color VarColor)

keywordColor :: DocH -> DocH
keywordColor = attr (Color KeywordColor)

markColor :: SyntaxForColor -> DocH -> DocH
markColor = attr . Color

specialFont :: DocH -> DocH
specialFont = attr SpecialFont


type PrettyH a = TranslateH a DocH

-- These are *recommendations* to the pretty printer.

data PrettyOptions = PrettyOptions
        { po_fullyQualified  :: Bool            -- Do you show fully qualified names?
        , po_exprTypes       :: ShowOption      -- Do you hide types, and type arguments, as <>?
        , po_typesForBinders :: ShowOption      -- Do you give the types for all bindings?
        , po_highlight       :: Maybe Path      -- This region should be highlighted (for sub-expression)
        , po_depth           :: Maybe Int       -- below this depth are ..., Nothing => infinite
        , po_notes           :: Bool            -- ^ notes might be added to output
        , po_ribbon          :: Float
        , po_width           :: Int
        } deriving Show

data ShowOption = Show | Abstract | Omit
        deriving (Eq, Ord, Show, Read)

instance Default PrettyOptions where
  def = PrettyOptions
        { po_fullyQualified  = False
        , po_exprTypes       = Abstract
        , po_typesForBinders = Omit
        , po_highlight       = Nothing
        , po_depth           = Nothing
        , po_notes           = False
        , po_ribbon          = 1.2
        , po_width           = 80
        }

-----------------------------------------------------------------

-- The characters for special symbols, which have a special alphabet

data SpecialSymbol
        = LambdaSymbol
        | TypeOfSymbol
        | RightArrowSymbol
        | TypeSymbol
        | TypeBindSymbol
        | ForallSymbol
        deriving (Show, Eq, Ord, Bounded, Enum)

class RenderSpecial a where
        renderSpecial :: SpecialSymbol -> a


instance RenderSpecial Char where
        renderSpecial LambdaSymbol        = '\\'  -- lambda
        renderSpecial TypeOfSymbol        = ':'   -- ::
        renderSpecial RightArrowSymbol    = '>'   -- ->
        renderSpecial TypeSymbol          = 'T'   -- <<type>>>
        renderSpecial TypeBindSymbol      = 'a'   -- a
        renderSpecial ForallSymbol      = 'F'   -- forall

newtype ASCII = ASCII String

instance Monoid ASCII where
        mempty = ASCII ""
        mappend (ASCII xs) (ASCII ys) = ASCII (xs ++ ys)

instance RenderSpecial ASCII where
        renderSpecial LambdaSymbol        = ASCII "\\"  -- lambda
        renderSpecial TypeOfSymbol        = ASCII "::"   -- ::
        renderSpecial RightArrowSymbol    = ASCII "->"   -- ->
        renderSpecial TypeSymbol          = ASCII "*"   -- <<type>>>
        renderSpecial TypeBindSymbol      = ASCII "*"   -- a
        renderSpecial ForallSymbol        = ASCII "\\/"

newtype Unicode = Unicode Char

instance RenderSpecial Unicode where
        renderSpecial LambdaSymbol        = Unicode '\x03BB'
        renderSpecial TypeOfSymbol        = Unicode '\x2237'     -- called PROPORTION
        renderSpecial RightArrowSymbol    = Unicode '\x2192'
        renderSpecial TypeSymbol          = Unicode '\x25b2'
        renderSpecial TypeBindSymbol      = Unicode '\x25B9'
        renderSpecial ForallSymbol        = Unicode '\x2200'

newtype LaTeX = LaTeX String

instance Monoid LaTeX where
        mempty = LaTeX ""
        mappend (LaTeX xs) (LaTeX ys) = LaTeX (xs ++ ys)

instance RenderSpecial LaTeX where
        renderSpecial LambdaSymbol        = LaTeX "\\ensuremath{\\lambda}"
        renderSpecial TypeOfSymbol        = LaTeX ":\\!:"  -- too wide
        renderSpecial RightArrowSymbol    = LaTeX "\\ensuremath{\\shortrightarrow}"
        renderSpecial TypeSymbol          = LaTeX "\\ensuremath{\\blacktriangle}"
        renderSpecial TypeBindSymbol      = LaTeX "\\ensuremath{\\triangleright}"
        renderSpecial ForallSymbol        = LaTeX "\\ensuremath{\\forall}"


newtype HTML = HTML String

instance Monoid HTML where
        mempty = HTML ""
        mappend (HTML xs) (HTML ys) = HTML (xs ++ ys)

instance RenderSpecial HTML where
        renderSpecial LambdaSymbol        = HTML "&#955;"
        renderSpecial TypeOfSymbol        = HTML "&#8759;"
        renderSpecial RightArrowSymbol    = HTML "&#8594;"
        renderSpecial TypeSymbol          = HTML "&#9650;"
        renderSpecial TypeBindSymbol      = HTML "&#9657;"
        renderSpecial ForallSymbol        = HTML "&#8704;"


renderSpecialFont :: (RenderSpecial a) => Char -> Maybe a
renderSpecialFont = fmap renderSpecial . flip M.lookup specialFontMap

specialFontMap :: M.Map Char SpecialSymbol
specialFontMap = M.fromList
                [ (renderSpecial s,s)
                | s <- [minBound..maxBound]
                ]


class (RenderSpecial a, Monoid a) => RenderCode a where
        rStart :: a
        rStart = mempty
        rEnd :: a
        rEnd = mempty

        rDoHighlight :: Bool -> [Attr]           -> a
        rPutStr      :: String -> a


-- This is what the pretty printer can see
data PrettyState = PrettyState
        { prettyPath  :: Path
        , prettyColor :: Maybe SyntaxForColor
        }

--stackToPrettyState :: [Attr] -> PrettyState
--stackToPrettyState =

renderCode :: RenderCode a => PrettyOptions -> DocH -> a
renderCode opts doc = rStart `mappend` PP.fullRender PP.PageMode w rib marker (\ _ -> rEnd) doc []
  where
          -- options
          w = po_width opts
          rib = po_ribbon opts

          marker ::  RenderCode a => PP.TextDetails HermitMark -> ([Attr] -> a) -> ([Attr]-> a)
          marker m rest cols@(SpecialFont:_) = case m of
                  PP.Chr ch   -> special [ch] `mappend` rest cols
                  PP.Str str  -> special str `mappend` rest cols
                  PP.PStr str -> special str `mappend` rest cols
                  PP.Mark (PopAttr)    -> rest (tail cols)
                  PP.Mark (PushAttr a) -> error "renderCode: can not have marks inside special symbols"
          marker m rest cols = case m of
                  PP.Chr ch   -> rPutStr [ch] `mappend` rest cols
                  PP.Str str  -> rPutStr str `mappend` rest cols
                  PP.PStr str -> rPutStr str `mappend` rest cols
                  PP.Mark (PushAttr a) ->
                        let cols' = a : cols in rDoHighlight True cols' `mappend` rest cols'
                  PP.Mark (PopAttr) -> do
                        let (_:cols') = cols in rDoHighlight False cols' `mappend` rest cols'

          special txt = mconcat [ code | Just code <- map renderSpecialFont txt ]


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
        ppH = arr (PP.text . showSDoc . ppr)

        ppModule :: PrettyH ModGuts
        ppModule = mg_module ^>> ppH

        ppDef :: PrettyH CoreDef
        ppDef = (\ (Def v e) -> (v,e)) ^>> ppH

--        arr (PP.text . ppr . mg_module)

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

--- Moving the renders back into the core hermit

-------------------------------------------------------------------------------

coreRenders :: [(String,Handle -> PrettyOptions -> DocH -> IO ())]
coreRenders =
        [ ("latex", \ h w doc -> do
                        let pretty = latexToString $ renderCode w doc
                        hPutStr h pretty)
        , ("html", \ h w doc -> do
                        let HTML pretty = renderCode w doc
                        hPutStr h pretty)
        , ("ascii", \ h w doc -> do
                        let (ASCII pretty) = renderCode w doc
                        hPutStrLn h pretty)
        , ("debug", \ h w doc -> do
                        let (DebugPretty pretty) = renderCode w doc
                        hPutStrLn h pretty)
        ]

latexVerbatim :: String -> LaTeX -> LaTeX
latexVerbatim str (LaTeX v) = LaTeX (str ++ v)

latexToString :: LaTeX -> String
latexToString (LaTeX orig) = unlines $ map trunkSpaces $ lines orig where
  trunkSpaces txt = case span isSpace txt of
                       ([],rest) -> rest
                       (pre,rest) -> "\\hspace{" ++ show (length pre) ++ "\\hermitspace}" ++ rest

instance RenderCode LaTeX where
        rPutStr txt  = LaTeX txt

        rDoHighlight False _ = LaTeX "}"
        rDoHighlight _ [] = LaTeX $ "{"
        rDoHighlight _ (Color col:_) = LaTeX $ "{" ++ case col of
                        KeywordColor -> "\\color{hermit:keyword}"       -- blue
                        SyntaxColor  -> "\\color{hermit:syntax}"        -- red
                        VarColor     -> ""
                        TypeColor    -> "\\color{hermit:type}"          -- green
                        LitColor     -> "\\color{hermit:lit}"           -- cyan
        rDoHighlight o (_:rest) = rDoHighlight o rest

        rEnd = LaTeX "\n" -- \\end{Verbatim}"

{- | Use css to do the colors
 -
 - > <style type="text/css">
 - >  .hermit-syntax {
 - >      color: red;
 - >  </style>
 -}

instance RenderCode HTML where
        rPutStr txt  = HTML txt

        rDoHighlight False _ = HTML "</span>"
        rDoHighlight _ [] = HTML $ "<span>"
        rDoHighlight _ (Color col:_) = HTML $ case col of
                        KeywordColor -> "<span class=\"hermit-keyword\">"       -- blue
                        SyntaxColor  -> "<span class=\"hermit-syntax\">"        -- red
                        VarColor     -> "<span>"
                        TypeColor    -> "<span class=\"hermit-type\">"          -- green
                        LitColor     -> "<span class=\"hermit-lit\">"           -- cyan
        rDoHighlight o (_:rest) = rDoHighlight o rest
        rEnd = HTML "\n"


instance RenderCode ASCII where
        rPutStr txt  = ASCII txt

        rDoHighlight _ _ = ASCII ""

        rEnd = ASCII "\n"

data DebugPretty = DebugPretty String

instance RenderSpecial DebugPretty where
        renderSpecial sym = DebugPretty ("{" ++ show sym ++ "}")

instance Monoid DebugPretty where
        mempty = DebugPretty ""
        mappend (DebugPretty xs) (DebugPretty ys) = DebugPretty $ xs ++ ys

instance RenderCode DebugPretty where
        rStart = DebugPretty "(START)\n"

        rPutStr txt  = DebugPretty txt

        rDoHighlight True  stk = DebugPretty $ show (True,stk)
        rDoHighlight False stk = DebugPretty $ show (False,stk)

        rEnd = DebugPretty "(END)\n"

