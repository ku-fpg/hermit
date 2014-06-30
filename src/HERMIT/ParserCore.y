{
{-# LANGUAGE CPP #-}
module HERMIT.ParserCore
    ( parseCore
    , parseCoreExprT
    , parse2BeforeT
    , parse3BeforeT
    , parse2beforeBiR
    , parse3beforeBiR
    , parse4beforeBiR
    , parse5beforeBiR
    , Token(..)
    , parseError
    , lexer
    ) where

import Control.Arrow
import Control.Monad.Reader
import Data.Char (isSpace, isDigit)

import HERMIT.Context
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name
import HERMIT.Syntax (isCoreInfixIdChar, isCoreIdFirstChar, isCoreIdChar)

import Language.KURE.MonadCatch (prefixFailMsg)
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
    | '(' ')'          {% lookupName "()" }
    | var              { $1 }
    | intlit           { $1 }
    | strlit           { $1 }

intlit : INTEGER       {% mkIntExpr' $1 } -- mkIntLit makes a primitive Int#

strlit : STRING        {% lift $ mkStringExpr $1 }

var : NAME             {% lookupName $1 }
{

mkIntExpr' :: Integer -> CoreParseM CoreExpr
#if __GLASGOW_HASKELL__ > 706
mkIntExpr' i = do
    dflags <- lift getDynFlags
    return $ mkIntExpr dflags i
#else
mkIntExpr' i = return $ mkIntExpr i
#endif

lookupName :: String -> CoreParseM CoreExpr
lookupName nm = do
    vset <- ask
    v <- lift $ prefixFailMsg (nm ++ " lookup: ") $ findId nm vset
    return $ varToCoreExpr v

type CoreParseM a = ReaderT VarSet HermitM a

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
    | Tdoublearrow
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
lexer ('_' :cs)    = fmap (Twild:)        $ lexer cs
lexer ('(' :cs)    = fmap (Toparen:)      $ lexer cs
lexer (')' :cs)    = fmap (Tcparen:)      $ lexer cs
lexer (':':':':cs) = fmap (Tcoloncolon:)  $ lexer cs
-- lexer (':' :cs)    = fmap (Tcolon:)       $ lexer cs
lexer ('\\':cs)    = fmap (Tlambda:)      $ lexer cs
lexer ('-':'>':cs) = fmap (Tarrow:)       $ lexer cs
lexer ('=':'>':cs) = fmap (Tdoublearrow:) $ lexer cs
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

parseCore :: BoundVars c => CoreString -> c -> HermitM CoreExpr
parseCore (CoreString s) c =
    case lexer s of
        Left msg -> fail msg
        Right tokens -> runReaderT (parser tokens) (boundVars c)

---------------------------------------------

-- These should probably go somewhere else.

-- | Parse a 'CoreString' to a 'CoreExpr', using the current context.
parseCoreExprT :: (BoundVars c, HasHermitMEnv m, HasLemmas m, HasStash m, LiftCoreM m)
               => CoreString -> Transform c m a CoreExpr
parseCoreExprT cs = contextonlyT $ embedHermitM . parseCore cs

parse2BeforeT :: (BoundVars c, HasHermitMEnv m, HasLemmas m, HasStash m, LiftCoreM m)
              => (CoreExpr -> CoreExpr -> Translate c m a b)
              -> CoreString -> CoreString -> Translate c m a b
parse2BeforeT f s1 s2 = parseCoreExprT s1 &&& parseCoreExprT s2 >>= uncurry f

parse3BeforeT :: (BoundVars c, HasHermitMEnv m, HasLemmas m, HasStash m, LiftCoreM m)
              => (CoreExpr -> CoreExpr -> CoreExpr -> Translate c m a b)
              -> CoreString -> CoreString -> CoreString -> Translate c m a b
parse3BeforeT f s1 s2 s3 = (parseCoreExprT s1 &&& parseCoreExprT s2) &&& parseCoreExprT s3 >>= (uncurry . uncurry $ f)

parse2beforeBiR :: (CoreExpr -> CoreExpr -> BiRewriteH a)
                -> CoreString -> CoreString -> BiRewriteH a
parse2beforeBiR f s1 s2 = beforeBiR (parseCoreExprT s1 &&& parseCoreExprT s2) (uncurry f)

parse3beforeBiR :: (CoreExpr -> CoreExpr -> CoreExpr -> BiRewriteH a)
                -> CoreString -> CoreString -> CoreString -> BiRewriteH a
parse3beforeBiR f s1 s2 s3 = beforeBiR ((parseCoreExprT s1 &&& parseCoreExprT s2) &&& parseCoreExprT s3) ((uncurry.uncurry) f)

parse4beforeBiR :: (CoreExpr -> CoreExpr -> CoreExpr -> CoreExpr -> BiRewriteH a)
                -> CoreString -> CoreString -> CoreString -> CoreString -> BiRewriteH a
parse4beforeBiR f s1 s2 s3 s4 = beforeBiR (((parseCoreExprT s1 &&& parseCoreExprT s2) &&& parseCoreExprT s3) &&& parseCoreExprT s4) ((uncurry.uncurry.uncurry) f)

parse5beforeBiR :: (CoreExpr -> CoreExpr -> CoreExpr -> CoreExpr -> CoreExpr -> BiRewriteH a)
                -> CoreString -> CoreString -> CoreString -> CoreString -> CoreString -> BiRewriteH a
parse5beforeBiR f s1 s2 s3 s4 s5 = beforeBiR ((((parseCoreExprT s1 &&& parseCoreExprT s2) &&& parseCoreExprT s3) &&& parseCoreExprT s4) &&& parseCoreExprT s5) ((uncurry.uncurry.uncurry.uncurry) f)

---------------------------------------------

}
