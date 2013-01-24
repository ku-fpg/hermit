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

%token
    '('     { ParenLeft }
    ')'     { ParenRight }
    '{'     { ScopeStart }
    '}'     { ScopeEnd }
    ';'     { StmtEnd }
    '\''    { Tick }
    quoted  { Quote $$ }
    ident   { Ident $$ }
    infixop { InfixOp $$ }

%%

StmtH : StmtH ';' scoped { $1 ++ [$3] }
      | StmtH ';'        { $1 }
      | scoped           { [$1] }
      | {- empty -}      { [] }

scoped : '{' StmtH '}' { ScopeH $2 }
       | E1            { ExprH (e1ToExprH $1) }

E1   : E2 infixop E1   { Infix $1 $2 $3 }
     | E2              { E2 $1 }

E2   : E2 Arg          { App $1 $2 }
     | E4              { E4 $1 }

Arg  : '\'' ident      { ArgSrc $2 }
     | quoted          { ArgCmd $1 }
     | E4              { ArgE4 $1 }

E4   : '(' E1 ')'      { Parens $2 }
     | ident           { Cmd $1 }

{

parseError :: [Token] -> a
parseError ts = error $ "parse error: " ++ show ts

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
    deriving (Eq, Show)

-- | Top level expression term.
--   Infix operators bind less tightly than application.
data E1 = Infix E2 String E1
        | E2 E2

-- | Expressions without infix operators in them.
data E2 = App E2 Arg
        | E4 E4

-- | Expressions that can be arguments in an application.
data Arg = ArgSrc String
         | ArgCmd String -- for quoted strings
         | ArgE4 E4

-- | Expressions that can be in any position of an application.
data E4 = Parens E1
        | Cmd String

e1ToExprH :: E1 -> ExprH
e1ToExprH (Infix e2 op e1) = AppH (AppH (CmdName op) (e2ToExprH e2)) (e1ToExprH e1)
e1ToExprH (E2 e2)          = e2ToExprH e2

e2ToExprH :: E2 -> ExprH
e2ToExprH (App e2 e3)      = AppH (e2ToExprH e2) (e3ToExprH e3)
e2ToExprH (E4 e4)          = e4ToExprH e4

e3ToExprH :: Arg -> ExprH
e3ToExprH (ArgSrc s)       = SrcName s
e3ToExprH (ArgCmd s)       = CmdName s
e3ToExprH (ArgE4 e4)       = e4ToExprH e4

e4ToExprH :: E4 -> ExprH
e4ToExprH (Parens e1)          = e1ToExprH e1
e4ToExprH (Cmd s)          = CmdName s

data Token
    = ParenLeft
    | ParenRight
    | ScopeStart
    | ScopeEnd
    | StmtEnd
    | Tick
    | Quote String
    | Ident String
    | InfixOp String
    deriving (Eq, Show)

lexer :: String -> Either String [Token]
lexer []        = Right []
lexer ('\n':cs) = fmap (StmtEnd:)    $ lexer cs
lexer (';' :cs) = fmap (StmtEnd:)    $ lexer cs
lexer ('(' :cs) = fmap (ParenLeft:)  $ lexer cs
lexer (')' :cs) = fmap (ParenRight:) $ lexer cs
lexer ('{' :cs) = fmap (ScopeStart:) $ lexer cs
lexer ('}' :cs) = fmap (ScopeEnd:)   $ lexer cs
lexer ('\'':cs) = fmap (Tick:)       $ lexer cs
lexer ('\"':cs) = let (str,rest) = span (/='\"') cs
                  in case rest of
                        ('\"':cs') -> fmap (Quote str:) $ lexer cs'
                        _          -> Left "lexer: no matching quote"
lexer s@(c:cs) | isSpace c = lexer cs
               | isIdFirstChar c = let (i,s') = span isIdChar s
                                   in fmap (Ident i:) $ lexer s'
               | isInfixId     c = let (op,s') = span isInfixId s
                                   in fmap (InfixOp op:) $ lexer s'
lexer s         = Left $ "lexer: no match on " ++ s

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
parseStmtsH = fmap parser . lexer

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
