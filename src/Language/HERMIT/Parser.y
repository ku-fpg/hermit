{
module Language.HERMIT.Parser
    ( parseStmtsH
    , unparseExprH
    , numStmtsH
    , ExprH(..)
    , StmtH(..)
    ) where

import Data.Char (isSpace, isAlphaNum)
import Data.List (intercalate)
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
    ';'     { StmtEnd }
    '\''    { Tick }
    core    { CoreString $$ }
    quoted  { Quote $$ }
    ident   { Ident $$ }
    infixop { InfixOp $$ }

%%

StmtH : StmtH ';' scoped { $1 ++ [$3] }
      | StmtH ';'        { $1 }
      | scoped           { [$1] }
      | {- empty -}      { [] }

scoped : '{' StmtH '}' { ScopeH $2 }
       | ExprH         { ExprH $1 }

-- | Top level expression term.
--   Infix operators bind less tightly than application.
ExprH : e2 infixop ExprH   { AppH (AppH (CmdName $2) $1) $3 }
      | e2                 { $1 }

-- | Expressions without infix operators in them.
e2   : e2 arg          { AppH $1 $2 }
     | e4              { $1 }

-- | Expressions that can be arguments in an application.
arg  : '\'' ident      { SrcName $2 }
     | quoted          { CmdName $1 }
     | core            { CoreExpr $1 }
     | e4              { $1 }

-- | Expressions that can be in any position of an application.
e4   : '(' ExprH ')'   { $2 }
     | ident           { CmdName $1 }

{

parseError :: [Token] -> Either String a
parseError ts = Left $ "parse error: " ++ show ts

-- | Nested lists to represent scoping structure.
data StmtH expr
    = ExprH expr
    | ScopeH [StmtH expr]
    deriving (Eq, Show)

-- | A simple expression language AST, for things parsed from 'String' or JSON structures.
data ExprH
    = SrcName String                -- ^ Variable names (refers to source code).
    | CmdName String                -- ^ Commands (to be looked up in 'Language.HERMIT.Dictionary').
    | AppH ExprH ExprH              -- ^ Application.
    | CoreExpr String               -- ^ Core Fragment TODO: change from String to CoreExpr
    deriving (Eq, Show)

data Token
    = ParenLeft
    | ParenRight
    | ScopeStart
    | ScopeEnd
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
lexer ('\"':cs)    = let (str,rest) = span (/='\"') cs
                     in case rest of
                           ('\"':cs') -> fmap (Quote str:) $ lexer cs'
                           _          -> Left "lexer: no matching quote"
lexer ('[':'|':cs) = do (str,cs') <- lexCore cs
                        fmap (CoreString str:) $ lexer cs'
lexer s@(c:cs)     | isSpace       c = lexer cs
                   | isIdFirstChar c = let (i,s') = span isIdChar s
                                       in fmap (Ident i:) $ lexer s'
                   | isInfixId     c = let (op,s') = span isInfixId s
                                       in fmap (InfixOp op:) $ lexer s'
lexer s            = Left $ "lexer: no match on " ++ s

lexCore :: String -> Either String (String,String)
lexCore ('|':']':rest) = Right ([],rest)
lexCore (c:cs)         = do (c',r) <- lexCore cs
                            return (c:c',r)
lexCore []             = Left "lexer: no closing |]"

---------------------------------------------

-- | Chars that are valid in identifiers anywhere.
isIdFirstChar :: Char -> Bool
isIdFirstChar c = isAlphaNum c || c `elem` "$[]:."

-- | Chars that are valid in identifiers, but not as the first character.
isIdChar :: Char -> Bool
isIdChar c = isIdFirstChar c || c `elem` "_-'"

-- | Chars that are valid in infix operators.
isInfixId :: Char -> Bool
isInfixId c = c `elem` "+*/._-:<>"

-- | Use ghci Parser.hs to run this test function.
test = do
    ln <- getLine
    case ln of
        "quit" -> return ()
        _      -> do print $ parseStmtsH ln
                     test

parseStmtsH :: String -> Either String [StmtH ExprH]
parseStmtsH s = lexer s >>= parser

-- TODO: This is a quick hack that's better than just saying "N"; I have no idea how accurate this is.

-- | Count the total number of statements.
numStmtH :: StmtH expr -> Int
numStmtH (ExprH _)   = 1
numStmtH (ScopeH ss) = numStmtsH ss

-- | Count the total number of statements.
numStmtsH :: [StmtH expr] -> Int
numStmtsH = sum . map numStmtH

---------------------------------------------

unparseExprH :: ExprH -> String
unparseExprH (SrcName nm) = "'" ++ nm
unparseExprH (CmdName nm)
        |  all isIdChar nm = nm
        | otherwise    = show nm     -- with quotes
unparseExprH (AppH (AppH (CmdName nm) e1) e2)
        | all isInfixId nm
        = unparseAtom e1 ++ " " ++ nm ++ " " ++ unparseAtom e2
unparseExprH (AppH e1 e2) = unparseExprH e1 ++ " " ++ unparseAtom e2

unparseAtom :: ExprH -> String
unparseAtom e@(AppH {}) = "(" ++ unparseExprH e ++ ")"
unparseAtom e           = unparseExprH e


unparseStmtH :: StmtH ExprH -> String
unparseStmtH (ExprH expr)   = unparseExprH expr
unparseStmtH (ScopeH stmts) = "{ " ++ unparseStmtsH stmts ++ "}"

unparseStmtsH :: [StmtH ExprH] -> String
unparseStmtsH stmts = intercalate " ; " (map unparseStmtH stmts)

---------------------------------------------

}
