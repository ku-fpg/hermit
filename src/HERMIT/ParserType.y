{
{-# LANGUAGE CPP #-}
module HERMIT.ParserType
#if __GLASGOW_HASKELL__ <= 706
    () where
#else
    ( parseType
    , parseTypeT
    ) where
#endif

import Control.Arrow
import Control.Monad.Reader
import Data.Char (isSpace, isDigit)

import HERMIT.Context
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name
import HERMIT.ParserCore
import HERMIT.Syntax (isCoreInfixIdChar, isCoreIdFirstChar, isCoreIdChar)

import Language.KURE.MonadCatch (prefixFailMsg)
}

%name parser
%tokentype { Token }
%error { parseError }
%monad { TypeParseM } { >>= } { return }

%token
    '%forall'  { Tforall }
    '%rec'     { Trec }
    '%let'     { Tlet }
    '%in'      { Tin }
    '%case'    { Tcase }
    '%of'      { Tof }
    '%cast'    { Tcast }
    '%note'    { Tnote }
    '%external'    { Texternal }
    '%local'   { Tlocal }
    '%_'       { Twild }
    '('        { Toparen }
    ')'        { Tcparen }
    '{'        { Tobrace }
    '}'        { Tcbrace }
    '#'        { Thash}
    '='        { Teq }
    ':'        { Tcolon }
    '::'       { Tcoloncolon }
    ':=:'      { Tcoloneqcolon }
    '*'        { Tstar }
    '->'       { Tarrow }
    '\\'       { Tlambda}
    '@'        { Tat }
    '.'        { Tdot }
    '?'        { Tquestion}
    ';'            { Tsemicolon }
    NAME       { Tname $$ }
    CNAME      { Tcname $$ }
    INTEGER    { Tinteger $$ }
    RATIONAL   { Trational $$ }
    STRING     { Tstring $$ }
    CHAR       { Tchar $$ }

%%

-- | Top level type term.
expr : app             { $1 }

app : app arg          { mkAppTy $1 $2 }
    | arg              { $1 }

arg : '(' expr ')'     { $2 }
    | '(' ')'          {% lookupName "()" }
    | var              { $1 }

var : NAME             {% lookupName $1 }
{

#if __GLASGOW_HASKELL__ <= 706
findType = error "findType cannot be called in < GHC 7.8"
#endif

lookupName :: String -> TypeParseM Type
lookupName nm = do
    c <- ask
    t <- lift $ prefixFailMsg (nm ++ " lookup: ") $ findType nm c
    return t

type TypeParseM a = ReaderT HermitC HermitM a

---------------------------------------------

parseType :: CoreString -> HermitC -> HermitM Type
parseType (CoreString s) c =
    case lexer s of
        Left msg -> fail msg
        Right tokens -> runReaderT (parser tokens) c

---------------------------------------------

-- | Parse a 'CoreString' to a 'Type', using the current context.
parseTypeT :: CoreString -> TransformH a Type
parseTypeT = contextonlyT . parseType

---------------------------------------------

}
