{
module HERMIT.Parser
    ( parseStmtsH
    , unparseExprH
    , numStmtsH
    , ExprH(..)
    ) where

import Data.Char (isSpace)
import Data.List (intercalate)

import HERMIT.Syntax (isScriptInfixIdChar, isScriptIdFirstChar, isScriptIdChar)

}

%name parser
%tokentype { Token }
%error { parseError }
%monad { Either String } { >>= } { return }

%token
    '('     { ParenLeft }
    ')'     { ParenRight }
    '{'     { ScopeStart }
    '}'     { ScopeEnd }
    '['     { ListStart }
    ','     { ListDelim }
    ']'     { ListEnd }
    ';'     { StmtEnd }
    '\''    { Tick }
    core    { CoreString $$ }
    quoted  { Quote $$ }
    ident   { Ident $$ }
    infixop { InfixOp $$ }

%%

scoped : '{' scoped { CmdName "{" : $2 }
       | '}' scoped { CmdName "}" : $2 }
       | slist      { $1 }

slist : stmts       { $1 }
      | {- empty -} { [] }

-- | Be really liberal about where ';' can be!
--   Recall that newlines are lexed as ';'
stmts : ExprH            { [$1] }
      | ExprH '}' scoped { [$1, CmdName "}"] ++ $3 }
      | ExprH ';' scoped { $1 : $3 }
      | ';' scoped       { $2 }

-- | Top level expression term.
--   Infix operators bind less tightly than application.
ExprH : e2 infixop ExprH   { AppH (AppH (CmdName $2) $1) $3 }
      | e2                 { $1 }

-- | Expressions without infix operators in them.
e2   : e2 arg          { AppH $1 $2 }
     | arg             { $1 }

-- | Expressions that can be arguments in an application.
arg  : '\'' ident      { SrcName $2 }
     | '\'' infixop    { SrcName $2 }
     | '\'' quoted     { SrcName $2 }
     | quoted          { CmdName $1 }
     | core            { CoreH $1 }
     | '[' elist ']'   { ListH $2 }
     | '(' ExprH ')'   { $2 }
     | ident           { CmdName $1 }

elist : exprs       { $1 }
      | {- empty -} { [] }

exprs : ExprH           { [$1] }
      | ExprH ',' exprs { $1 : $3 }
{

parseError :: [Token] -> Either String a
parseError ts = Left $ "parse error: " ++ show ts

-- | A simple expression language AST, for things parsed from 'String' or JSON structures.
data ExprH
    = SrcName String                -- ^ Variable names (refers to source code).
    | CmdName String                -- ^ Commands (to be looked up in 'HERMIT.Dictionary').
    | AppH ExprH ExprH              -- ^ Application.
    | CoreH String                  -- ^ Core Fragment
    | ListH [ExprH]                 -- ^ List of expressions
    deriving (Eq, Show)

data Token
    = ParenLeft
    | ParenRight
    | ScopeStart
    | ScopeEnd
    | ListStart
    | ListDelim
    | ListEnd
    | StmtEnd
    | Tick
    | CoreString String
    | Quote String
    | Ident String
    | InfixOp String
    deriving (Eq, Show)

lexer :: String -> Either String [Token]
lexer []           = Right []
lexer ('\n':cs)    = fmap (StmtEnd:)    $ lexer cs
lexer (';' :cs)    = fmap (StmtEnd:)    $ lexer cs
lexer ('(' :cs)    = fmap (ParenLeft:)  $ lexer cs
lexer (')' :cs)    = fmap (ParenRight:) $ lexer cs
lexer ('{' :cs)    = fmap (ScopeStart:) $ lexer cs
lexer ('}' :cs)    = fmap (ScopeEnd:)   $ lexer cs
lexer ('\'':cs)    = fmap (Tick:)       $ lexer cs
lexer ('\"':cs)    = do (str,cs') <- lexString cs
                        fmap (Quote str:) $ lexer cs'
lexer ('[':'|':cs) = do (str,cs') <- lexCore cs
                        fmap (CoreString str:) $ lexer cs'
lexer ('-':'-':cs) = let (_,s') = span (/= '\n') cs in lexer s'
lexer ('[' :cs)    = fmap (ListStart:)  $ lexer cs
lexer (',' :cs)    = fmap (ListDelim:)  $ lexer cs
lexer (']' :cs)    = fmap (ListEnd:)    $ lexer cs
lexer s@(c:cs)     | isSpace             c = lexer cs
                   | isScriptIdFirstChar c = let (i,s') = span isScriptIdChar s
                                              in fmap (Ident i:) $ lexer s'
                   | isScriptInfixIdChar c = let (op,s') = span isScriptInfixIdChar s
                                              in fmap (InfixOp op:) $ lexer s'
lexer s            = Left $ "lexer: no match on " ++ s

lexString :: String -> Either String (String,String)
lexString ('\"':cs)      = Right ([],cs)
lexString ('\\':'\"':cs) = do (c',r) <- lexString cs
                              return ('"':c',r)
lexString (c:cs)         = do (c',r) <- lexString cs
                              return (c:c',r)
lexString []             = Left "lexer: no matching quote"

lexCore :: String -> Either String (String,String)
lexCore ('|':']':rest) = Right ([],rest)
lexCore (c:cs)         = do (c',r) <- lexCore cs
                            return (c:c',r)
lexCore []             = Left "lexer: no closing |]"

---------------------------------------------

-- | Use ghci Parser.hs to run this test function.
test = do
    ln <- getLine
    case ln of
        "quit" -> return ()
        _      -> do print $ lexer ln
                     print $ parseStmtsH ln
                     test

parseStmtsH :: String -> Either String [ExprH]
parseStmtsH s = lexer s >>= parser

numStmtsH :: [ExprH] -> Int
numStmtsH = length . filter isCounted
    where isCounted (CmdName "{") = False
          isCounted (CmdName "}") = False
          isCounted _             = True
---------------------------------------------

unparseExprH :: ExprH -> String
unparseExprH (SrcName nm)
    | nm /= "" && (all isScriptInfixIdChar nm || isScriptIdFirstChar (head nm) && all isScriptIdChar (tail nm)) = "'" ++ nm
    | otherwise = "'\"" ++ concatMap escape nm ++ "\""
        where escape '\"' = "\\\""
              escape c    = [c]
unparseExprH (CmdName nm)
    | nm == "{"             = "{ "
    | nm == "}"             = " }"
    | all isScriptIdChar nm = nm
    | otherwise             = show nm     -- with quotes
unparseExprH (AppH (AppH (CmdName nm) e1) e2)
    | all isScriptInfixIdChar nm
    = unparseAtom e1 ++ " " ++ nm ++ " " ++ unparseAtom e2
unparseExprH (AppH e1 e2) = unparseExprH e1 ++ " " ++ unparseAtom e2
unparseExprH (CoreH s)    = "[|" ++ s ++ "|]"
unparseExprH (ListH es)   = "[" ++ intercalate "," (map unparseExprH es) ++ "]"

unparseAtom :: ExprH -> String
unparseAtom e@(AppH {}) = "(" ++ unparseExprH e ++ ")"
unparseAtom e           = unparseExprH e

---------------------------------------------

}
