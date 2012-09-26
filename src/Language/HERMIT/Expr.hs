module Language.HERMIT.Expr
        ( -- * HERMIT Expressions

          -- | This is the /untyped/ command and control language for HERMIT.
          ExprH(..)
        , StmtH(..)
        , parseExprH
        , parseStmtsH
        , unparseExprH
        , unparseStmtH
        , unparseStmtsH
        , numStmtsH
        ) where

import Control.Applicative ((<$>))
import Data.Char
import Data.List

---------------------------------------------

-- | A simple expression language AST, for things parsed from 'String' or JSON structures.
data ExprH
        = SrcName String                -- ^ Variable names (refers to source code).
        | CmdName String                -- ^ Commands (to be looked up in 'Language.HERMIT.Dictionary').
        | AppH ExprH ExprH              -- ^ Application.
        deriving (Eq, Show)

-- | Nested lists to represent scoping structure.
data StmtH expr
        = ExprH expr
        | ScopeH [StmtH expr]
        deriving Show

data Box e = InfixableExpr e | Box e deriving Show

---------------------------------------------

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
        |  all isId nm = nm
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

-- Cheap and cheerful parser. Pretty hacky for now

parse :: ReadS a -> String -> Either String a
parse p str = case p str of
                (a,rest) : _  | all isSpace rest -> Right a
                _                                -> Left $ "User error, cannot parse: " ++ str

many :: ReadS a -> ReadS [a]
many p inp =
     some p inp ++
     [ ([], inp) ]

some :: ReadS a -> ReadS [a]
some p inp =
     [ (x:xs,inp2)
     | (x,inp1)  <- p inp
     , (xs,inp2) <- many p inp1
     ]

bind :: ReadS a -> (a -> ReadS b) -> ReadS b
bind m k inp =
        [ (b,inp2)
        | (a,inp1) <- m inp
        , (b,inp2) <- k a inp1
        ]

---------------------------------------------


-- | Parse an expression.
parseExprH :: String -> Either String ExprH
parseExprH = parse parseExprH1

-- | Parse a list of statements, seperated by semicolons.
parseStmtsH :: String -> Either String [StmtH ExprH]
parseStmtsH = parse parseExprsH'

---------------------------------------------

parseExprsH' :: ReadS [StmtH ExprH]
parseExprsH' inp =
        (many (item ";")                 `bind` \ _ -> -- another hack
        (parseTopExprH1                  `bind` (\ a ->
        (many (item ";")                 `bind` \ _ -> -- complete hack, needed fixed with real parser
        (parseExprsH'                    `bind` (\ as ->
        (\ inp' -> [(a:as,inp')]))))))) inp ++  [ ([], inp) ]



parseTopExprH1 :: ReadS (StmtH ExprH)
parseTopExprH1 inp =
        (parseExprH1 `bind` \ es inp1 -> [(ExprH es,inp1)]) inp ++
        [ (ScopeH es,inp3)
        | ("{",inp1) <- parseToken inp
        , (es,inp2)   <- parseExprsH' inp1
        , ("}",inp3) <- parseToken inp2
        ]


parseExprH0 :: ReadS (Box ExprH)
parseExprH0 inp =
        [ (Box (CmdName str),inp1)
        | (str,inp1) <- parseToken inp
        , isAlphaNum (head str) || head str == ':'    -- commands can start with :
        , all isId (tail str)
        ] ++
        [ (InfixableExpr (CmdName str),inp1)
        | (str,inp1) <- parseToken inp
        , all isInfixId str
        ] ++
        [ (Box (SrcName str),inp2)
        | ("'",inp1) <- parseToken inp
        , (str,inp2) <- parseToken inp1
        ] ++
        [ (Box (CmdName $ chomp '"' str),inp1)
        | (str@('"':_),inp1) <- lex inp
        ] ++
        [ (Box e,inp3)
        | ("(",inp1) <- parseToken inp
        , (e,inp2)   <- parseExprH1 inp1
        , (")",inp3) <- parseToken inp2
        ]
    where chomp _  [] = []
          chomp ch s@(c:cs) | c == ch && last cs == ch = init cs
                            | otherwise = s

parseExprH1 :: ReadS ExprH
parseExprH1 = some parseExprH0 `bind` \ es inp ->
        case mkAppH es id [] of
          Nothing -> []
          Just r  -> [(r,inp)]

-- TODO: Assoc to the right, want assoc to the left.
mkAppH :: [Box ExprH] -> (ExprH -> ExprH) -> [ExprH] -> Maybe ExprH
mkAppH (Box e:es)             ops        rs = mkAppH es ops (rs ++ [e])
mkAppH (InfixableExpr e:es)   ops        rs = maybe Nothing (\ lhs ->
                                                mkAppH es (ops . AppH (AppH e lhs)) []
                                                ) (mkAppH' rs)
mkAppH []                     ops rs        = ops <$> mkAppH' rs

mkAppH' :: [ExprH] -> Maybe ExprH
mkAppH' (r:rs) = Just $ foldl AppH r rs
mkAppH' []     = Nothing

--mkAppH (e:es)             = foldl AppH (f e) (map f es)
--  where f (InfixableExpr e) = e
--        f (Box e) = e


item :: String -> ReadS ()
item str inp =
        [ ((),rest)
        | (tok,rest) <- parseToken inp
        , tok == str
        ]

parseToken :: ReadS String
parseToken []        = []
parseToken ('\n':cs) = [(";",cs)]               -- yes, really
parseToken ('(' :cs) = [("(",cs)]
parseToken (')' :cs) = [(")",cs)]
parseToken ('{' :cs) = [("{",cs)]
parseToken ('}' :cs) = [("}",cs)]
parseToken (';' :cs) = [(";",cs)]
parseToken ('\'':cs) = [("'",cs)]
parseToken ('\"':cs) = [("\"",cs)]
parseToken (c   :cs) | isSpace c = parseToken cs
                     | c == ':'       = [let (a,b) = span isId cs in (c:a,b) ]
                     | isAlphaNum c   = [span isId (c:cs)]
                     | isInfixId c    = [span isInfixId (c:cs)]
parseToken _         = []

---------------------------------------------

isId :: Char -> Bool
isId c = isAlphaNum c || c `elem` "_-'"

isInfixId :: Char -> Bool
isInfixId c = c `elem` "+*/._-:<>"


---------------------------------------------


