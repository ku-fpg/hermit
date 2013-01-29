{
module Language.HERMIT.ParserCore (parseCore) where

import Control.Monad.Reader
import Data.Char (isSpace, isAlpha, isAlphaNum)
-- import Data.List (intercalate)

import GhcPlugins

import Language.HERMIT.Context
import Language.HERMIT.Monad

import Language.Haskell.TH as TH
}

%name parser
%tokentype { Token }
%error { parseError }
%monad { CoreParseM } { >>= } { return }

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

-- | Top level expression term.
expr : NAME   {% asks (findBoundVars (TH.mkName $1)) >>= \ nms ->
                 case nms of
                    [] -> fail $ "core parse error: " ++ $1 ++ " not found in context."
                    [nm] -> return $ Var nm
                    _    -> fail $ "core parse error: " ++ $1 ++ " bound multiple times in context."
              }
{

type CoreParseM a = ReaderT HermitC HermitM a

parseError :: [Token] -> CoreParseM a
parseError ts = fail $ "core parse error: " ++ show ts

data Token
    = Tforall
    | Trec
    | Tlet
    | Tin
    | Tcase
    | Tof
    | Tcast
    | Tnote
    | Texternal
    | Tlocal
    | Twild --
    | Toparen --
    | Tcparen --
    | Tobrace
    | Tcbrace
    | Thash
    | Teq
    | Tcolon --
    | Tcoloncolon --
    | Tcoloneqcolon
    | Tstar
    | Tarrow
    | Tlambda --
    | Tat
    | Tdot
    | Tquestion
    | Tsemicolon
    | Tname String
    | Tcname String
    | Tinteger Integer
    | Trational Float
    | Tstring String
    | Tchar Char
    deriving (Eq, Show)

lexer :: String -> Either String [Token]
lexer []           = Right []
lexer ('_' :cs)    = fmap (Twild:)       $ lexer cs
lexer ('(' :cs)    = fmap (Toparen:)     $ lexer cs
lexer (')' :cs)    = fmap (Tcparen:)     $ lexer cs
lexer (':':':':cs) = fmap (Tcoloncolon:) $ lexer cs
lexer (':' :cs)    = fmap (Tcolon:)      $ lexer cs
lexer ('\\':cs)    = fmap (Tlambda:)     $ lexer cs
lexer ('-':'>':cs) = fmap (Tarrow:)      $ lexer cs
lexer ('\"':cs)    = let (str,rest) = span (/='\"') cs
                     in case rest of
                           ('\"':cs') -> fmap (Tstring str:) $ lexer cs'
                           _          -> Left "lexer: no matching quote"
lexer s@(c:cs)     | isSpace       c = lexer cs
                   | isIdFirstChar c = let (i,s') = span isIdChar s
                                       in fmap (Tname i:) $ lexer s'
                   | isInfixId     c = let (op,s') = span isInfixId s
                                       in fmap (Tname op:) $ lexer s'
lexer s            = Left $ "lexer: no match on " ++ s

---------------------------------------------

-- | Chars that are valid in identifiers anywhere.
isIdFirstChar :: Char -> Bool
isIdFirstChar c = c `elem` "_$[]:." || isAlpha c

-- | Chars that are valid in identifiers, but not as the first character.
isIdChar :: Char -> Bool
isIdChar c = isAlphaNum c || c `elem` "-'" || isIdFirstChar c

-- | Chars that are valid in infix operators.
isInfixId :: Char -> Bool
isInfixId c = c `elem` "+*/._-:<>"

parseCore :: String -> HermitC -> HermitM CoreExpr
parseCore s c = case lexer s of
                    Left msg -> fail msg
                    Right tokens -> runReaderT (parser tokens) c

}
