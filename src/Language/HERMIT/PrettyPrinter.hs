module Language.HERMIT.PrettyPrinter where

import Text.PrettyPrint.MarkedHughesPJ
import Language.HERMIT.HermitKure
import Control.Applicative


-- A HERMIT document
type DocH = MDoc HermitMark

-- These are the zero-width marks on the document
data HermitMark
        = PushAttr Attr
        | PopAttr

-- These are the attributes
data Attr = PathAttr [Int]
          | Color SyntaxForColor

data SyntaxForColor = Keyword | Syntax

type PrettyH a = TranslateH a DocH

astCorePrettyH :: PrettyH Core
astCorePrettyH = pure (text "<<pretty>>")



