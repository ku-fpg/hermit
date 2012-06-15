-- Expr is the *untyped* command and control language for HERMIT.

module Language.HERMIT.HermitExpr
        ( ExprH(..)
        , parseExprH
        , parseStmtsH
        ) where

import Control.Applicative ((<$>))
import Data.Char

---------------------------------------------

-- Our local version of Expr, for things parsed from string or JSON structures.
data ExprH
        = SrcName String                -- variable names (refer to source code)
        | CmdName String                -- commands (to be looked up in Dictionary) or strings; same thing
        | AppH ExprH ExprH              -- application
        deriving Show

data StmtH expr
        = ExprH expr
        | ScopeH [StmtH expr]
        deriving Show

data Box e = InfixableExpr e | Box e
        deriving Show
---------------------------------------------

-- Cheap and cheerful parser. Pretty hacky for now

parse :: ReadS a -> String -> Either String a
parse p str = case p str of
                (a,rest) : _  | all isSpace rest -> Right a
                _                                -> Left $ "Bad parse for: " ++ str

many :: ReadS a -> ReadS [a]
many p = \ inp ->
     some p inp ++
     [ ([], inp) ]

some :: ReadS a -> ReadS [a]
some p = \ inp ->
     [ (x:xs,inp2)
     | (x,inp1)  <- p inp
     , (xs,inp2) <- many p inp1
     ]

bind :: ReadS a -> (a -> ReadS b) -> ReadS b
bind m k = \ inp ->
        [ (b,inp2)
        | (a,inp1) <- m inp
        , (b,inp2) <- k a inp1
        ]

---------------------------------------------


-- | parse an expression.
parseExprH :: String -> Either String ExprH
parseExprH = parse parseExprH1

-- | parse a list of statements, seperated by semicolon
parseStmtsH :: String -> Either String [StmtH ExprH]
parseStmtsH = parse parseExprsH'

---------------------------------------------

parseExprsH' :: ReadS [StmtH ExprH]
parseExprsH' =
        parseTopExprH1 `bind` (\ a ->
        many (some (item ";") `bind` \ _ -> parseTopExprH1) `bind` (\ as ->
        (\ inp -> [(a:as,inp)])))

parseTopExprH1 :: ReadS (StmtH ExprH)
parseTopExprH1 = \ inp ->
        (parseExprH1 `bind` \ es -> \ inp1 -> [(ExprH es,inp1)]) inp ++
        [ (ScopeH es,inp3)
        | ("{",inp1) <- parseToken inp
        , (es,inp2)   <- parseExprsH' inp1
        , ("}",inp3) <- parseToken inp2
        ]


parseExprH0 :: ReadS (Box ExprH)
parseExprH0 = \ inp ->
        [ (Box $ CmdName str,inp1)
        | (str,inp1) <- parseToken inp
        , all isId str
        ] ++
        [ (InfixableExpr $ CmdName str,inp1)
        | (str,inp1) <- parseToken inp
        , all isInfixId str
        ] ++
        [ (Box $ SrcName str,inp2)
        | ("'",inp1) <- parseToken inp
        , (str,inp2) <- parseToken inp1
        ] ++
        [ (Box $ CmdName $ chomp '"' str,inp1)
        | (str@('"':_),inp1) <- lex inp
        ] ++
        [ (Box $ e,inp3)
        | ("(",inp1) <- parseToken inp
        , (e,inp2)   <- parseExprH1 inp1
        , (")",inp3) <- parseToken inp2
        ]
    where chomp _  [] = []
          chomp ch s@(c:cs) | c == ch && last cs == ch = init cs
                            | otherwise = s

parseExprH1 :: ReadS ExprH
parseExprH1 = some parseExprH0 `bind` \ es -> \ inp ->
        case mkAppH es id [] of
          Nothing -> []
          Just r  -> [(r,inp)]

-- Infix hook: TODO
-- infix version, only one level for now
--mkAppH a [CmdName fn,b] | all (`elem` ".->") fn
--                        = foldr AppH (CmdName fn) [a,b]
mkAppH :: [Box ExprH] -> (ExprH -> ExprH) -> [ExprH] -> Maybe ExprH
--mkAppH (InfixableExpr e:es)   ops rs@(_:_)     = mkAppH es (mkAppH' rs)
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
item str = \ inp ->
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
                     | isAlphaNum c   = [span isId (c:cs)]
                     | isInfixId c    = [span isInfixId (c:cs)]
parseToken _         = []

---------------------------------------------

isId :: Char -> Bool
isId c = isAlphaNum c || c `elem` "_-"

isInfixId :: Char -> Bool
isInfixId c = c `elem` "+._-:<>"


---------------------------------------------


