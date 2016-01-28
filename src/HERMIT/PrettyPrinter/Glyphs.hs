{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
module HERMIT.PrettyPrinter.Glyphs where

import Data.Semigroup (Semigroup(..))
import Data.Typeable

import HERMIT.Kure
import HERMIT.External
import HERMIT.PrettyPrinter.Common

import GHC.Generics

import System.Console.ANSI

-- | Glyph
data Glyph = Glyph { gText :: String
                   , gStyle :: Maybe SyntaxForColor
                   } deriving Show

-- | Glyphs
newtype Glyphs = Glyphs [Glyph] deriving (Generic, Show)

withStyle :: Maybe SyntaxForColor -> String -> IO ()
withStyle Nothing    str = putStr str
withStyle (Just sty) str = do
  setSGR $ styleSGR sty
  putStr str
  setSGR [Reset]

withNoStyle :: Maybe SyntaxForColor -> String -> IO ()
withNoStyle _ str = putStr str

styleSGR :: SyntaxForColor -> [SGR]
styleSGR KeywordColor  = [simpleColor Blue]
styleSGR SyntaxColor   = [simpleColor Red]
styleSGR IdColor       = []
styleSGR CoercionColor = [simpleColor Yellow]
styleSGR TypeColor     = [simpleColor Green]
styleSGR LitColor      = [simpleColor Cyan]
styleSGR WarningColor  = [SetColor Background Vivid Yellow
                         ,SetColor Foreground Dull  Black
                         ]

simpleColor :: Color -> SGR
simpleColor = SetColor Foreground Vivid

instance RenderSpecial Glyphs where
    renderSpecial sym        = Glyphs [ Glyph [ch] (Just style) ]
        where Unicode ch = renderSpecial sym
              style =
                case sym of
                  TypeSymbol     -> TypeColor
                  TypeBindSymbol -> TypeColor
                  _              -> SyntaxColor

instance Monoid Glyphs where
    mempty = Glyphs mempty
    mappend = (<>)

instance Semigroup Glyphs where
    Glyphs rs1 <> Glyphs rs2 =
        Glyphs . flattenGlyphs . mergeGlyphs $ rs1 ++ rs2

flattenGlyphs :: [Glyph] -> [Glyph]
flattenGlyphs = go Nothing
    where go :: Maybe SyntaxForColor -> [Glyph] -> [Glyph]
          go _ [] = []
          go s (Glyph str Nothing:r) = Glyph str s : go s r
          go _ (Glyph [] s@Just{}:r) = go s r
          go s (g:r) = g : go s r

mergeGlyphs :: [Glyph] -> [Glyph]
mergeGlyphs [] = []
mergeGlyphs [r] = [r]
mergeGlyphs (g:h:r) = case merge g h of
                        Left g' -> mergeGlyphs (g':r)
                        Right (g',h') -> g' : mergeGlyphs (h':r)
    where merge (Glyph s1 Nothing)  (Glyph s2 Nothing) =
              Left $ Glyph (s1 ++ s2) Nothing
          merge (Glyph [] Just{}) g2@(Glyph [] Just{}) = Left g2
          merge g1 g2 = Right (g1,g2)

instance RenderCode Glyphs where
    rPutStr txt = Glyphs [ Glyph txt Nothing, Glyph [] (Just IdColor) ]
    rDoHighlight _ [] = mempty
    rDoHighlight _ (Color col:_) = Glyphs [Glyph [] (Just col)]
    rDoHighlight o (_:rest) = rDoHighlight o rest

-- External Instances
data TransformLCoreGlyphsBox = TransformLCoreGlyphsBox (TransformH LCore Glyphs) deriving Typeable

instance Extern (TransformH LCore Glyphs) where
    type Box (TransformH LCore Glyphs) = TransformLCoreGlyphsBox
    box = TransformLCoreGlyphsBox
    unbox (TransformLCoreGlyphsBox i) = i

data TransformLCoreTCGlyphsBox = TransformLCoreTCGlyphsBox (TransformH LCoreTC Glyphs) deriving Typeable

instance Extern (TransformH LCoreTC Glyphs) where
    type Box (TransformH LCoreTC Glyphs) = TransformLCoreTCGlyphsBox
    box = TransformLCoreTCGlyphsBox
    unbox (TransformLCoreTCGlyphsBox i) = i
