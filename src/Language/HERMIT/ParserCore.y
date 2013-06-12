{
{-# LANGUAGE CPP #-}
module Language.HERMIT.ParserCore (parseCore) where

import Control.Monad.Reader
import Data.Char (isSpace, isDigit)

import GhcPlugins

import Language.HERMIT.Context
import Language.HERMIT.External
import Language.HERMIT.Monad
import Language.HERMIT.Primitive.Common
import Language.HERMIT.Syntax (isCoreInfixIdChar, isCoreIdFirstChar, isCoreIdChar)

import Language.KURE.MonadCatch (prefixFailMsg)

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
expr : app             { $1 }

app : app arg          { App $1 $2 }
    | arg              { $1 }

arg : '(' expr ')'     { $2 }
    | '(' ')'          {% lookupName "()" Var }
    | var              { $1 }
    | intlit           { $1 }
    | strlit           { $1 }

intlit : INTEGER       {% mkIntExpr' $1 } -- mkIntLit makes a primitive Int#

strlit : STRING        {% lift $ mkStringExpr $1 }

var : NAME             {% lookupName $1 varToCoreExpr }
{

mkIntExpr' :: Integer -> CoreParseM CoreExpr
#if __GLASGOW_HASKELL__ > 706
mkIntExpr' i = do
    dflags <- lift getDynFlags
    return $ mkIntExpr dflags i
#else
mkIntExpr' i = return $ mkIntExpr i
#endif

lookupName :: String -> (Id -> CoreExpr) -> CoreParseM CoreExpr
lookupName nm k = do
    c <- ask
    v <- lift $ prefixFailMsg (nm ++ " lookup: ") $ findId (TH.mkName nm) c
    return (k v)

type CoreParseM a = ReaderT HermitC HermitM a

parseError :: Monad m => [Token] -> m a
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
-- lexer (':' :cs)    = fmap (Tcolon:)      $ lexer cs
lexer ('\\':cs)    = fmap (Tlambda:)     $ lexer cs
lexer ('-':'>':cs) = fmap (Tarrow:)      $ lexer cs
lexer ('\"':cs)    = let (str,rest) = span (/='\"') cs
                     in case rest of
                           ('\"':cs') -> fmap (Tstring str:) $ lexer cs'
                           _          -> Left "lexer: no matching quote"
lexer s@(c:cs) | isSpace           c = lexer cs
               | isDigit           c = let (i,s') = span isDigit s
                                         in fmap (Tinteger (read i):) $ lexer s'
               | isCoreIdFirstChar c = let (i,s') = span isCoreIdChar s
                                         in fmap (Tname i:) $ lexer s'
               | isCoreInfixIdChar c = let (op,s') = span isCoreInfixIdChar s
                                         in fmap (Tname op:) $ lexer s'
lexer s            = Left $ "lexer: no match on " ++ s

---------------------------------------------

parseCore :: CoreString -> HermitC -> HermitM CoreExpr
parseCore (CoreString s) c =
    case lexer s of
        Left msg -> fail msg
        Right tokens -> runReaderT (parser tokens) c
}
