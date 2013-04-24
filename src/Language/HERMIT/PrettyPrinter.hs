{-# LANGUAGE FlexibleInstances #-}

module Language.HERMIT.PrettyPrinter where

import GhcPlugins hiding ((<>))

import Text.PrettyPrint.MarkedHughesPJ as PP
import Language.HERMIT.Kure
import Language.HERMIT.Core
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
        | CoercionColor
        | TypeColor
        | LitColor
    deriving Show

attr :: Attr -> DocH -> DocH
attr a p = mark (PushAttr a) <> p <> mark PopAttr

-- Hack, till we get 'PathAttr' working properly
-- The problem is that attributes span over multiple lines,
-- messing up the latex output

attrP :: Path -> DocH -> DocH
attrP _ doc = doc -- attr . PathAttr

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
        | CoercionSymbol
        | TypeSymbol
        | TypeBindSymbol
        | ForallSymbol
        deriving (Show, Eq, Ord, Bounded, Enum)

class RenderSpecial a where
        renderSpecial :: SpecialSymbol -> a


-- This instance is special.  It is used as an index, forming an association list.
-- Thus all of the rhs must be distinct characters.
-- Think of RenderSpecial as a special font.
instance RenderSpecial Char where
        renderSpecial LambdaSymbol        = '\\'  -- lambda
        renderSpecial TypeOfSymbol        = ':'   -- ::
        renderSpecial RightArrowSymbol    = '>'   -- ->
        renderSpecial CoercionSymbol      = 'C'   -- <<coercion>>>
        renderSpecial TypeSymbol          = 'T'   -- <<type>>>
        renderSpecial TypeBindSymbol      = 't'   -- <<type binding>>
        renderSpecial ForallSymbol        = 'F'   -- forall

newtype ASCII = ASCII String

instance Monoid ASCII where
        mempty = ASCII ""
        mappend (ASCII xs) (ASCII ys) = ASCII (xs ++ ys)

instance RenderSpecial ASCII where
        renderSpecial LambdaSymbol        = ASCII "\\"  -- lambda
        renderSpecial TypeOfSymbol        = ASCII "::"   -- ::
        renderSpecial RightArrowSymbol    = ASCII "->"   -- ->
        renderSpecial CoercionSymbol      = ASCII "~"   -- <<coercion>>>
        renderSpecial TypeSymbol          = ASCII "*"   -- <<type>>>
        renderSpecial TypeBindSymbol      = ASCII "*"   -- <<type>>>
        renderSpecial ForallSymbol        = ASCII "\\/"

newtype Unicode = Unicode Char

instance RenderSpecial Unicode where
        renderSpecial LambdaSymbol        = Unicode '\x03BB'
        renderSpecial TypeOfSymbol        = Unicode '\x2237'     -- called PROPORTION
        renderSpecial RightArrowSymbol    = Unicode '\x2192'
        renderSpecial CoercionSymbol      = Unicode '\x25A0'
        renderSpecial TypeSymbol          = Unicode '\x25b2'
        renderSpecial TypeBindSymbol      = Unicode '\x25b2' -- Unicode '\x25B9'
        renderSpecial ForallSymbol        = Unicode '\x2200'

newtype LaTeX = LaTeX String

instance Monoid LaTeX where
        mempty = LaTeX ""
        mappend (LaTeX xs) (LaTeX ys) = LaTeX (xs ++ ys)

instance RenderSpecial LaTeX where
        renderSpecial LambdaSymbol        = LaTeX "\\ensuremath{\\lambda}"
        renderSpecial TypeOfSymbol        = LaTeX ":\\!:"  -- too wide
        renderSpecial RightArrowSymbol    = LaTeX "\\ensuremath{\\shortrightarrow}"
        renderSpecial CoercionSymbol      = LaTeX "\\ensuremath{\\blacksquare}"
        renderSpecial TypeSymbol          = LaTeX "\\ensuremath{\\blacktriangle}"
        renderSpecial TypeBindSymbol      = LaTeX "\\ensuremath{\\blacktriangle}" -- LaTeX "\\ensuremath{\\triangleright}"
        renderSpecial ForallSymbol        = LaTeX "\\ensuremath{\\forall}"


newtype HTML = HTML String

instance Monoid HTML where
        mempty = HTML ""
        mappend (HTML xs) (HTML ys) = HTML (xs ++ ys)

instance RenderSpecial HTML where
        renderSpecial LambdaSymbol        = HTML "&#955;"
        renderSpecial TypeOfSymbol        = HTML "&#8759;"
        renderSpecial RightArrowSymbol    = HTML "&#8594;"
        renderSpecial CoercionSymbol      = HTML "&#9632;"
        renderSpecial TypeSymbol          = HTML "&#9650;"
        renderSpecial TypeBindSymbol      = HTML "&#9650;" -- HTML "&#9657;"
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
                  PP.Mark (PopAttr)    ->
                        let (_:cols') = cols in rDoHighlight False cols' `mappend` rest cols'
                  PP.Mark (PushAttr _) -> error "renderCode: can not have marks inside special symbols"
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
        <+ promoteT (ppProg   :: PrettyH CoreProg)
        <+ promoteT (ppH      :: PrettyH CoreBind)
        <+ promoteT (ppDef    :: PrettyH CoreDef)
        <+ promoteT (ppH      :: PrettyH CoreExpr)
        <+ promoteT (ppH      :: PrettyH CoreAlt)
  where

        ppH :: (Outputable a) => PrettyH a
        ppH = contextfreeT $ \e -> do
            dynFlags <- getDynFlags
            return $ PP.text $ showSDoc dynFlags $ ppr e

        ppModule :: PrettyH ModGuts
        ppModule = mg_module ^>> ppH

        ppProg :: PrettyH CoreProg
        ppProg = progToBinds ^>> ppH

        ppDef :: PrettyH CoreDef
        ppDef = defToIdExpr ^>> ppH

--        arr (PP.text . ppr . mg_module)

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
                        KeywordColor  -> "\\color{hermit:keyword}"       -- blue
                        SyntaxColor   -> "\\color{hermit:syntax}"        -- red
                        VarColor      -> ""
                        CoercionColor -> "\\color{hermit:coercion}"      -- yellow
                        TypeColor     -> "\\color{hermit:type}"          -- green
                        LitColor      -> "\\color{hermit:lit}"           -- cyan
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
                        KeywordColor  -> "<span class=\"hermit-keyword\">"       -- blue
                        SyntaxColor   -> "<span class=\"hermit-syntax\">"        -- red
                        VarColor      -> "<span>"
                        CoercionColor -> "<span class=\"hermit-coercion\">"      -- yellow
                        TypeColor     -> "<span class=\"hermit-type\">"          -- green
                        LitColor      -> "<span class=\"hermit-lit\">"           -- cyan
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

