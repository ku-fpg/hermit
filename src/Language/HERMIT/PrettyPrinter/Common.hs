{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, TypeFamilies, InstanceSigs,
             MultiParamTypeClasses, RankNTypes, FlexibleContexts #-}

module Language.HERMIT.PrettyPrinter.Common
    ( -- * Documents
      DocH
    , Attr(..)
    , attrP
      -- ** Colors
    , coercionColor
    , idColor
    , keywordColor
    , markColor
    , typeColor
    , ShowOption(..)
    , specialFont
    , SpecialSymbol(..)
    , SyntaxForColor(..)
      -- * Renderers
    , coreRenders
    , renderCode
    , RenderCode(..)
    , renderSpecial
    , RenderSpecial
    , Unicode(..)
      -- * Pretty Printer Traversals
    , PrettyH
    , liftPrettyH
    , PrettyC(..)
    , initPrettyC
    , liftPrettyC
    , TranslateDocH(..)
    , TranslateCoreTCDocHBox(..)
      -- * Pretty Printer Options
    , PrettyOptions(..)
    , updateCoShowOption
    , updateTypeShowOption
    , updateWidthOption
      -- * Utilities
    , hlist
    , vlist
    ) where

import GhcPlugins hiding (($$), (<>), (<+>))

import Data.Char
import Data.Default
import Data.Monoid hiding ((<>))
import qualified Data.Map as M
import Data.Typeable

import Language.HERMIT.Context
import Language.HERMIT.Core
import Language.HERMIT.External
import Language.HERMIT.Kure
import Language.HERMIT.Monad

import System.IO

import Text.PrettyPrint.MarkedHughesPJ as PP

-- A HERMIT document
type DocH = MDoc HermitMark

-- newtype wrapper for proper instance selection
newtype TranslateDocH a = TranslateDocH { unTranslateDocH :: PrettyC -> PrettyH a -> TranslateH a DocH }

data TranslateCoreTCDocHBox = TranslateCoreTCDocHBox (TranslateDocH CoreTC) deriving Typeable

instance Extern (TranslateDocH CoreTC) where
    type Box (TranslateDocH CoreTC) = TranslateCoreTCDocHBox
    box = TranslateCoreTCDocHBox
    unbox (TranslateCoreTCDocHBox i) = i

-- These are the zero-width marks on the document
data HermitMark
        = PushAttr Attr
        | PopAttr
    deriving Show

-- These are the attributes
data Attr = PathAttr AbsolutePathH
          | Color SyntaxForColor
          | SpecialFont
    deriving (Eq, Show)

data SyntaxForColor             -- (suggestion)
        = KeywordColor          -- bold
        | SyntaxColor
        | IdColor
        | CoercionColor
        | TypeColor
        | LitColor
        | WarningColor          -- highlight problems like unbound variables
    deriving (Eq, Show)

attr :: Attr -> DocH -> DocH
attr a p = mark (PushAttr a) <> p <> mark PopAttr

attrP :: AbsolutePathH -> DocH -> DocH
attrP = attr . PathAttr

idColor :: DocH -> DocH
idColor = markColor IdColor

typeColor :: DocH -> DocH
typeColor = markColor TypeColor

coercionColor :: DocH -> DocH
coercionColor = markColor CoercionColor

keywordColor :: DocH -> DocH
keywordColor = markColor KeywordColor

markColor :: SyntaxForColor -> DocH -> DocH
markColor = attr . Color

specialFont :: DocH -> DocH
specialFont = attr SpecialFont

type PrettyH a = Translate PrettyC HermitM a DocH
-- TODO: change monads to something more restricted?

-- | Context for PrettyH translations.
data PrettyC = PrettyC { prettyC_path    :: AbsolutePath Crumb
                       , prettyC_vars    :: VarSet
                       , prettyC_options :: PrettyOptions
                       }

------------------------------------------------------------------------

instance ReadPath PrettyC Crumb where
  absPath :: PrettyC -> AbsolutePath Crumb
  absPath = prettyC_path
  {-# INLINE absPath #-}

instance ExtendPath PrettyC Crumb where
  (@@) :: PrettyC -> Crumb -> PrettyC
  c @@ n = c { prettyC_path = prettyC_path c @@ n }
  {-# INLINE (@@) #-}

instance AddBindings PrettyC where
  addHermitBindings :: [(Var,HermitBindingSite)] -> PrettyC -> PrettyC
  addHermitBindings vbs c = c { prettyC_vars = foldr (flip extendVarSet) (prettyC_vars c) (map fst vbs) }
                            -- let vhbs = [ (v, (0,b)) | (v,b) <- vbs ] -- TODO: do we care about depth?
                            --  in c { prettyC_bindings = M.fromList vhbs `M.union` prettyC_bindings c }
  {-# INLINE addHermitBindings #-}

-- instance ReadBindings PrettyC where
--   hermitDepth :: PrettyC -> BindingDepth
--   hermitDepth = prettyC_depth

--   hermitBindings :: PrettyC -> M.Map Var HermitBinding
--   hermitBindings = prettyC_bindings
--   {-# INLINE hermitBindings #-}

instance BoundVars PrettyC where
  boundVars :: PrettyC -> VarSet
  boundVars = prettyC_vars

------------------------------------------------------------------------

liftPrettyH :: (ReadBindings c, ReadPath c Crumb) => PrettyOptions -> PrettyH a -> Translate c HermitM a DocH
liftPrettyH = liftContext . liftPrettyC

liftPrettyC :: (ReadBindings c, ReadPath c Crumb) => PrettyOptions -> c -> PrettyC
liftPrettyC opts c = PrettyC { prettyC_path    = absPath c
                             , prettyC_vars    = boundVars c
                             , prettyC_options = opts}

initPrettyC :: PrettyOptions -> PrettyC
initPrettyC opts = PrettyC
                      { prettyC_path    = mempty
                      , prettyC_vars    = emptyVarSet
                      , prettyC_options = opts
                      }

-- These are *recommendations* to the pretty printer.

data PrettyOptions = PrettyOptions
        { po_fullyQualified  :: Bool            -- ^ Do you show fully qualified names?
        , po_exprTypes       :: ShowOption      -- ^ Do you hide types, and type arguments, as <>?
        , po_coercions       :: ShowOption      -- ^ Do you hide coercions?
        , po_typesForBinders :: ShowOption      -- ^ Do you give the types for all bindings?
        , po_focus           :: Maybe PathH     -- ^ This region should be highlighted (is the current focus)
        , po_depth           :: Maybe Int       -- ^ below this depth are ..., Nothing => infinite
        , po_notes           :: Bool            -- ^ notes might be added to output
        , po_ribbon          :: Float
        , po_width           :: Int
        } deriving Show

data ShowOption = Show | Abstract | Omit | Kind deriving (Eq, Ord, Show, Read)

-- Types don't have a Kind showing option.
updateTypeShowOption :: ShowOption -> PrettyOptions -> PrettyOptions
updateTypeShowOption Kind po = po
updateTypeShowOption opt  po = po { po_exprTypes = opt }

updateCoShowOption :: ShowOption -> PrettyOptions -> PrettyOptions
updateCoShowOption opt po  = po { po_coercions = opt }

updateWidthOption :: Int -> PrettyOptions -> PrettyOptions
updateWidthOption w po = po { po_width = w }

instance Default PrettyOptions where
  def = PrettyOptions
        { po_fullyQualified  = False
        , po_exprTypes       = Abstract
        , po_coercions       = Abstract
        , po_typesForBinders = Omit
        , po_focus           = Nothing
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
        | CastSymbol
        | CoercionSymbol
        | CoercionBindSymbol
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
        renderSpecial CastSymbol          = '#'   -- "|>"
        renderSpecial CoercionSymbol      = 'C'   -- <<coercion>>>
        renderSpecial CoercionBindSymbol  = 'c'   -- <<coercion>>>
        renderSpecial TypeSymbol          = 'T'   -- <<type>>>
        renderSpecial TypeBindSymbol      = 't'   -- <<type binding>>
        renderSpecial ForallSymbol        = 'F'   -- forall

newtype ASCII = ASCII String

instance Monoid ASCII where
        mempty = ASCII ""
        mappend (ASCII xs) (ASCII ys) = ASCII (xs ++ ys)

instance RenderSpecial ASCII where
        renderSpecial LambdaSymbol        = ASCII "\\"   -- lambda
        renderSpecial TypeOfSymbol        = ASCII "::"   -- ::
        renderSpecial RightArrowSymbol    = ASCII "->"   -- ->
        renderSpecial CastSymbol          = ASCII "|>"   -- "|>"
        renderSpecial CoercionSymbol      = ASCII "~#"   -- <<coercion>>>
        renderSpecial CoercionBindSymbol  = ASCII "~#"   -- <<coercion binding>>>
        renderSpecial TypeSymbol          = ASCII "*"    -- <<type>>>
        renderSpecial TypeBindSymbol      = ASCII "*"    -- <<type binding>>>
        renderSpecial ForallSymbol        = ASCII "\\/"

newtype Unicode = Unicode Char

instance RenderSpecial Unicode where
        renderSpecial LambdaSymbol        = Unicode '\x03BB'
        renderSpecial TypeOfSymbol        = Unicode '\x2237'     -- called PROPORTION
        renderSpecial RightArrowSymbol    = Unicode '\x2192'
        renderSpecial CastSymbol          = Unicode '\x25B9'
        renderSpecial CoercionSymbol      = Unicode '\x25A0'
        renderSpecial CoercionBindSymbol  = Unicode '\x25A1'
        renderSpecial TypeSymbol          = Unicode '\x25b2'
        renderSpecial TypeBindSymbol      = Unicode '\x25b3'
        renderSpecial ForallSymbol        = Unicode '\x2200'

newtype LaTeX = LaTeX String

instance Monoid LaTeX where
        mempty = LaTeX ""
        mappend (LaTeX xs) (LaTeX ys) = LaTeX (xs ++ ys)

instance RenderSpecial LaTeX where
        renderSpecial LambdaSymbol        = LaTeX "\\ensuremath{\\lambda}"
        renderSpecial TypeOfSymbol        = LaTeX ":\\!:"  -- too wide
        renderSpecial RightArrowSymbol    = LaTeX "\\ensuremath{\\shortrightarrow}"
        renderSpecial CastSymbol          = LaTeX "\\ensuremath{\\triangleright}"
        renderSpecial CoercionSymbol      = LaTeX "\\ensuremath{\\blacksquare}"
        renderSpecial CoercionBindSymbol  = LaTeX "\\ensuremath{\\square}"
        renderSpecial TypeSymbol          = LaTeX "\\ensuremath{\\blacktriangle}"
        renderSpecial TypeBindSymbol      = LaTeX "\\ensuremath{\\vartriangle}"
        renderSpecial ForallSymbol        = LaTeX "\\ensuremath{\\forall}"


newtype HTML = HTML String

instance Monoid HTML where
        mempty = HTML ""
        mappend (HTML xs) (HTML ys) = HTML (xs ++ ys)

instance RenderSpecial HTML where
        renderSpecial LambdaSymbol        = HTML "&#955;"
        renderSpecial TypeOfSymbol        = HTML "&#8759;"
        renderSpecial RightArrowSymbol    = HTML "&#8594;"
        renderSpecial CastSymbol          = HTML "&#9657;"
        renderSpecial CoercionSymbol      = HTML "&#9632;"
        renderSpecial CoercionBindSymbol  = HTML "&#9633;"
        renderSpecial TypeSymbol          = HTML "&#9650;"
        renderSpecial TypeBindSymbol      = HTML "&#9651;"
        renderSpecial ForallSymbol        = HTML "&#8704;"


renderSpecialFont :: RenderSpecial a => Char -> Maybe a
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

    rDoHighlight :: Maybe Attr  -- ^ Attr just popped, if any
                 -> [Attr]      -- ^ Attr stack
                 -> a

    rPutStr      :: String -> a

renderCode :: RenderCode a => PrettyOptions -> DocH -> a
renderCode opts doc = rStart `mappend` PP.fullRender PP.PageMode w rib marker (\ _ -> rEnd) doc []
  where
          -- options
          w = po_width opts
          rib = po_ribbon opts

          marker :: RenderCode a => PP.TextDetails HermitMark -> ([Attr] -> a) -> ([Attr]-> a)
          marker m rest as@(SpecialFont:_) = case m of
                  PP.Chr ch   -> special [ch] `mappend` rest as
                  PP.Str str  -> special str `mappend` rest as
                  PP.PStr str -> special str `mappend` rest as
                  PP.Mark PopAttr ->
                        let (a:as') = as in rDoHighlight (Just a) as' `mappend` rest as'
                  PP.Mark (PushAttr _) -> error "renderCode: can not have marks inside special symbols"
          marker m rest as = case m of
                  PP.Chr ch   -> rPutStr [ch] `mappend` rest as
                  PP.Str str  -> rPutStr str `mappend` rest as
                  PP.PStr str -> rPutStr str `mappend` rest as
                  PP.Mark (PushAttr a) ->
                        let as' = a : as in rDoHighlight Nothing as' `mappend` rest as'
                  PP.Mark PopAttr -> do
                        let (a:as') = as in rDoHighlight (Just a) as' `mappend` rest as'

          special txt = mconcat [ code | Just code <- map renderSpecialFont txt ]


-- Other options for pretty printing:
-- * Does a top level program should function names, or complete listings?

--- Moving the renders back into the core hermit

-------------------------------------------------------------------------------

coreRenders :: [(String,Handle -> PrettyOptions -> DocH -> IO ())]
coreRenders =
        [ ("latex", \ h opts doc -> do
                        let pretty = latexToString $ renderCode opts doc
                        hPutStr h pretty)
        , ("html", \ h opts doc -> do
                        let HTML pretty = renderCode opts doc
                        hPutStr h pretty)
        , ("ascii", \ h opts doc -> do
                        let (ASCII pretty) = renderCode opts doc
                        hPutStrLn h pretty)
        , ("debug", \ h opts doc -> do
                        let (DebugPretty pretty) = renderCode opts doc
                        hPutStrLn h pretty)
        ]

-- latexVerbatim :: String -> LaTeX -> LaTeX
-- latexVerbatim str (LaTeX v) = LaTeX (str ++ v)

latexToString :: LaTeX -> String
latexToString (LaTeX orig) = unlines $ map trunkSpaces $ lines orig where
  trunkSpaces txt = case span isSpace txt of
                       ([],rest) -> rest
                       (pre,rest) -> "\\hspace{" ++ show (length pre) ++ "\\hermitspace}" ++ rest

instance RenderCode LaTeX where
        rPutStr txt  = LaTeX txt

        -- Latex throws away PathAttr
        rDoHighlight (Just _) _ = LaTeX "}"
        rDoHighlight _ [] = LaTeX $ "{"
        rDoHighlight _ (Color col:_) = LaTeX $ "{" ++ case col of
                        KeywordColor  -> "\\color{hermit:keyword}"       -- blue
                        SyntaxColor   -> "\\color{hermit:syntax}"        -- red
                        IdColor       -> ""
                        CoercionColor -> "\\color{hermit:coercion}"      -- yellow
                        TypeColor     -> "\\color{hermit:type}"          -- green
                        LitColor      -> "\\color{hermit:lit}"           -- cyan
                        WarningColor  -> "\\color{hermit:warning}"       -- black on yellow
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

        rDoHighlight (Just _) _ = HTML "</span>"
        rDoHighlight _ [] = HTML $ "<span>"
        rDoHighlight _ (Color col:_) = HTML $ case col of
                        KeywordColor  -> "<span class=\"hermit-keyword\">"       -- blue
                        SyntaxColor   -> "<span class=\"hermit-syntax\">"        -- red
                        IdColor       -> "<span>"
                        CoercionColor -> "<span class=\"hermit-coercion\">"      -- yellow
                        TypeColor     -> "<span class=\"hermit-type\">"          -- green
                        LitColor      -> "<span class=\"hermit-lit\">"           -- cyan
                        WarningColor  -> "<span class=\"hermit-warning\">"       -- black on yellow
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

        rDoHighlight Nothing stk = DebugPretty $ show (True,stk)
        rDoHighlight (Just _) stk = DebugPretty $ show (False,stk)

        rEnd = DebugPretty "(END)\n"

-------------------------------------------------------------------------------

listify :: (MDoc a -> MDoc a -> MDoc a) -> [MDoc a] -> MDoc a
listify _  []     = PP.text "[]"
listify op (d:ds) = op (PP.text "[ " <> d) (foldr (\e es -> op (PP.text ", " <> e) es) (PP.text "]") ds)

-- | like vcat and hcat, only make the list syntax explicit
vlist, hlist :: [MDoc a] -> MDoc a
vlist = listify ($$)
hlist = listify (<+>)

-------------------------------------------------------------------------------
