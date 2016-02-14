{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module HERMIT.PrettyPrinter.Common
    ( -- * Documents
      DocH
    , Attr(..)
    , HTML(..)
    , ASCII(..)
      -- ** Colors
    , coercionColor
    , idColor
    , keywordColor
    , syntaxColor
    , markColor
    , typeColor
    , ShowOption(..)
    , specialFont
    , SpecialSymbol(..)
    , SyntaxForColor(..)
    , specialSymbol
    , symbol
    , keyword
      -- * Renderers
    , coreRenders
    , renderCode
    , RenderCode(..)
    , renderSpecial
    , RenderSpecial
    , Unicode(..)
      -- * Pretty Printer Traversals
    , PrettyPrinter(..)
    , PrettyH
    , PrettyHLCoreBox(..)
    , PrettyHLCoreTCBox(..)
    , liftPrettyH
    , PrettyC(..)
    , initPrettyC
    , liftPrettyC
      -- * Pretty Printer Options
    , PrettyOptions(..)
    , updateCoShowOption
    , updateTypeShowOption
    , updateWidthOption
      -- * Utilities
    , pad
    , hlist
    , vlist
    , showRole
#if __GLASGOW_HASKELL__ > 710
    , showVis
#endif
    , HermitMark(..) -- AJG: for now
    ) where

import Data.Char
import Data.Default.Class
import qualified Data.Map as M
import qualified Data.Semigroup as Semigroup

import GHC.Generics

import HERMIT.Context
import HERMIT.Core
import HERMIT.External
import HERMIT.GHC hiding (($$), (<>), (<+>), char, text, keyword)
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Monad

import Text.PrettyPrint.MarkedHughesPJ as PP

showRole :: Role -> String
showRole Nominal          = "N"
showRole Representational = "R"
showRole Phantom          = "P"

#if __GLASGOW_HASKELL__ > 710
showVis :: VisibilityFlag -> String
showVis Visible   = "Visible"
showVis Specified = "Specified"
showVis Invisible = "Invisible"
#endif

-- A HERMIT document
type DocH = MDoc HermitMark

-- These are the zero-width marks on the document
data HermitMark
        = PushAttr Attr
        | PopAttr
    deriving (Show, Generic)

-- These are the attributes
data Attr = Color SyntaxForColor
          | SpecialFont
    deriving (Eq, Show, Generic)

data SyntaxForColor             -- (suggestion)
        = KeywordColor          -- bold
        | SyntaxColor
        | IdColor
        | CoercionColor
        | TypeColor
        | LitColor
        | WarningColor          -- highlight problems like unbound variables
    deriving (Eq, Show, Generic)

attr :: Attr -> DocH -> DocH
attr a p = mark (PushAttr a) <> p <> mark PopAttr

idColor :: DocH -> DocH
idColor = markColor IdColor

typeColor :: DocH -> DocH
typeColor = markColor TypeColor

coercionColor :: DocH -> DocH
coercionColor = markColor CoercionColor

keywordColor :: DocH -> DocH
keywordColor = markColor KeywordColor

syntaxColor :: DocH -> DocH
syntaxColor = markColor SyntaxColor

markColor :: SyntaxForColor -> DocH -> DocH
markColor = attr . Color

specialFont :: DocH -> DocH
specialFont = attr SpecialFont

specialSymbol :: SpecialSymbol -> DocH
specialSymbol = markColor SyntaxColor . specialFont . char . renderSpecial

symbol :: Char -> DocH
symbol = markColor SyntaxColor . char

keyword :: String -> DocH
keyword = markColor KeywordColor . text

data PrettyPrinter = PP { pLCoreTC :: PrettyH LCoreTC
                        , pOptions :: PrettyOptions
                        , pTag     :: String
                        }

instance Extern PrettyPrinter where
    type Box PrettyPrinter = PrettyPrinter
    box i = i
    unbox i = i

type PrettyH a = Transform PrettyC HermitM a DocH
-- TODO: change monads to something more restricted?

data PrettyHLCoreBox = PrettyHLCoreBox (PrettyH LCore)

instance Extern (PrettyH LCore) where
    type Box (PrettyH LCore) = PrettyHLCoreBox
    box = PrettyHLCoreBox
    unbox (PrettyHLCoreBox i) = i

data PrettyHLCoreTCBox = PrettyHLCoreTCBox (PrettyH LCoreTC)

instance Extern (PrettyH LCoreTC) where
    type Box (PrettyH LCoreTC) = PrettyHLCoreTCBox
    box = PrettyHLCoreTCBox
    unbox (PrettyHLCoreTCBox i) = i

-------------------------------------------------------------------------------

-- | Context for PrettyH translations.
data PrettyC = PrettyC { prettyC_path    :: AbsolutePathH
                       , prettyC_vars    :: M.Map Var AbsolutePathH
                       , prettyC_options :: PrettyOptions
                       , prettyC_lemmas  :: Lemmas
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
  addHermitBindings :: [(Var,HermitBindingSite,AbsolutePathH)] -> PrettyC -> PrettyC
  addHermitBindings vbs c = c { prettyC_vars = M.union (prettyC_vars c) (M.fromList [ (i,p) | (i,_,p) <- vbs ]) }
  {-# INLINE addHermitBindings #-}

instance BoundVars PrettyC where
  boundVars :: PrettyC -> VarSet
  boundVars = mkVarSet . M.keys . prettyC_vars

instance HasEmptyContext PrettyC where
  setEmptyContext :: PrettyC -> PrettyC
  setEmptyContext c = c { prettyC_path = mempty
                        , prettyC_vars = M.empty }

instance LemmaContext PrettyC where
    addAntecedent nm l c = c { prettyC_lemmas = M.insert nm l (prettyC_lemmas c) }
    getAntecedents = prettyC_lemmas

------------------------------------------------------------------------

liftPrettyH :: (LemmaContext c, ReadBindings c, ReadPath c Crumb) => PrettyOptions -> Transform PrettyC HermitM a b -> Transform c HermitM a b
liftPrettyH = liftContext . liftPrettyC

liftPrettyC :: (LemmaContext c, ReadBindings c, ReadPath c Crumb) => PrettyOptions -> c -> PrettyC
liftPrettyC opts c = PrettyC { prettyC_path    = absPath c
                             , prettyC_vars    = M.fromList [ (i,hbPath b) | (i,b) <- M.toList (hermitBindings c) ]
                             , prettyC_options = opts
                             , prettyC_lemmas  = getAntecedents c
                             }

initPrettyC :: PrettyOptions -> PrettyC
initPrettyC opts = PrettyC
                      { prettyC_path    = mempty
                      , prettyC_vars    = M.empty
                      , prettyC_options = opts
                      , prettyC_lemmas  = M.empty
                      }

-- These are *recommendations* to the pretty printer.
-- AJG: These seem to be in two places, the PrettyC context, and inside PrettyPrinter.

data PrettyOptions = PrettyOptions
        { po_fullyQualified  :: Bool            -- ^ Do you show fully qualified names?
        , po_exprTypes       :: ShowOption      -- ^ Do you hide types, and type arguments, as <>?
        , po_coercions       :: ShowOption      -- ^ Do you hide coercions?
        , po_typesForBinders :: ShowOption      -- ^ Do you give the types for all bindings?
        , po_showUniques     :: Bool            -- ^ Append uniques to OccNames? (Like GHC does)
        , po_focus           :: Maybe PathH     -- ^ This region should be highlighted (is the current focus)
        , po_depth           :: Maybe Int       -- ^ below this depth are ..., Nothing => infinite
        , po_notes           :: Bool            -- ^ notes might be added to output
        , po_ribbon          :: Float
        , po_width           :: Int             -- AJG: The width is not a pretty option, but rather a render option (?)
        } deriving (Generic, Show)

data ShowOption = Show | Abstract | Detailed | Omit | Kind
  deriving (Eq, Generic, Ord, Show, Read)

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
        , po_coercions       = Kind
        , po_typesForBinders = Omit
        , po_showUniques     = False
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
        | ConjSymbol
        | DisjSymbol
        | ImplSymbol
        | EquivSymbol
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
        renderSpecial ConjSymbol          = '^'   -- conjunction
        renderSpecial DisjSymbol          = 'v'   -- disjunction
        renderSpecial ImplSymbol          = '?'   -- implication (we can't use >, because it is used for ->)
        renderSpecial EquivSymbol         = '='   -- equivalence

newtype ASCII = ASCII String

instance Monoid ASCII where
        mempty = ASCII ""
        mappend = (Semigroup.<>)

instance Semigroup.Semigroup ASCII where
        ASCII xs <> ASCII ys = ASCII (xs ++ ys)

instance RenderSpecial ASCII where
        renderSpecial LambdaSymbol        = ASCII "\\"   -- lambda
        renderSpecial TypeOfSymbol        = ASCII "::"   -- ::
        renderSpecial RightArrowSymbol    = ASCII "->"   -- ->
        renderSpecial CastSymbol          = ASCII "|>"   -- "|>"
        renderSpecial CoercionSymbol      = ASCII "~#"   -- <<coercion>>>
        renderSpecial CoercionBindSymbol  = ASCII "~#"   -- <<coercion binding>>>
        renderSpecial TypeSymbol          = ASCII "*"    -- <<type>>>
        renderSpecial TypeBindSymbol      = ASCII "*"    -- <<type binding>>>
        renderSpecial ForallSymbol        = ASCII "forall"
        renderSpecial ConjSymbol          = ASCII "^"    -- conjunction
        renderSpecial DisjSymbol          = ASCII "v"    -- disjunction
        renderSpecial ImplSymbol          = ASCII "=>"   -- implication
        renderSpecial EquivSymbol         = ASCII "="    -- equivalence

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
        renderSpecial ConjSymbol          = Unicode '\x2227'
        renderSpecial DisjSymbol          = Unicode '\x2228'
        renderSpecial ImplSymbol          = Unicode '\x21D2'
        renderSpecial EquivSymbol         = Unicode '\x2261'

newtype LaTeX = LaTeX String

instance Monoid LaTeX where
        mempty = LaTeX ""
        mappend = (Semigroup.<>)

instance Semigroup.Semigroup LaTeX where
        LaTeX xs <> LaTeX ys = LaTeX (xs ++ ys)

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
        renderSpecial ConjSymbol          = LaTeX "\\ensuremath{\\wedge}"
        renderSpecial DisjSymbol          = LaTeX "\\ensuremath{\\lor}"
        renderSpecial ImplSymbol          = LaTeX "\\ensuremath{\\Rightarrow}"
        renderSpecial EquivSymbol         = LaTeX "\\ensuremath{\\equiv}"


newtype HTML = HTML String

instance Monoid HTML where
        mempty = HTML ""
        mappend = (Semigroup.<>)

instance Semigroup.Semigroup HTML where
        HTML xs <> HTML ys = HTML (xs ++ ys)

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
        renderSpecial ConjSymbol          = HTML "&and;"
        renderSpecial DisjSymbol          = HTML "&or;"
        renderSpecial ImplSymbol          = HTML "&rArr;"
        renderSpecial EquivSymbol         = HTML "&equiv;"

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

coreRenders :: [(String, PrettyOptions -> DocH -> String)]
coreRenders =
        [ ("latex", \ opts doc -> latexToString $ renderCode opts doc)
        , ("html", \ opts doc -> let HTML str = renderCode opts doc in str)
        , ("ascii", \ opts doc -> let ASCII str = renderCode opts doc in str)
        , ("debug", \ opts doc -> let DebugPretty str = renderCode opts doc in str)
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
        mappend = (Semigroup.<>)

instance Semigroup.Semigroup DebugPretty where
        DebugPretty xs <> DebugPretty ys = DebugPretty $ xs ++ ys

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

-- | wrap a document in spaces
pad :: MDoc a -> MDoc a
pad d = char ' ' <> d <> char ' '

-------------------------------------------------------------------------------
