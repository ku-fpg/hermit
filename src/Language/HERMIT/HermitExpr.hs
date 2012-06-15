-- Expr is the *untyped* command and control language for HERMIT.

module Language.HERMIT.HermitExpr
        ( ExprH(..)
        , parseExprH
        , parseExprsH
        ) where

import Data.Char

---------------------------------------------

-- Our local version of Expr, for things parsed from string or JSON structures.
data ExprH
        = SrcName String                -- variable names (refer to source code)
        | CmdName String                -- commands (to be looked up in Dictionary) or strings; same thing
        | AppH ExprH ExprH              -- application
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

parseExprH :: String -> Either String ExprH
parseExprH = parse parseExprH1

parseExprsH :: String -> Either String [ExprH]
parseExprsH = parse parseExprsH'

---------------------------------------------

parseExprsH' :: ReadS [ExprH]
parseExprsH' =
        parseExprH1 `bind` (\ a ->
        many (some (item ";") `bind` \ _ -> parseExprH1) `bind` (\ as ->
        (\ inp -> [(a:as,inp)])))

parseExprH0 :: ReadS ExprH
parseExprH0 = \ inp ->
        [ (CmdName str,inp1)
        | (str,inp1) <- parseToken inp
        , all isId str
        ] ++
        [ (SrcName str,inp2)
        | ("'",inp1) <- parseToken inp
        , (str,inp2) <- parseToken inp1
        ] ++
        [ (CmdName $ chomp '"' str,inp1)
        | (str@('"':_),inp1) <- lex inp
        ] ++
        [ (e,inp3)
        | ("(",inp1) <- parseToken inp
        , (e,inp2)   <- parseExprH1 inp1
        , (")",inp3) <- parseToken inp2
        ]
    where chomp _  [] = []
          chomp ch s@(c:cs) | c == ch && last cs == ch = init cs
                            | otherwise = s

parseExprH1 :: ReadS ExprH
parseExprH1 = \ inp ->
        [ (mkAppH e es,inp2)
        | (e,inp1)  <- parseExprH0 inp
        , (es,inp2) <- parseExprsH1 inp1
        ]

-- Infix hook: TODO
-- infix version, only one level for now
--mkAppH a [CmdName fn,b] | all (`elem` ".->") fn
--                        = foldr AppH (CmdName fn) [a,b]
mkAppH :: ExprH -> [ExprH] -> ExprH
mkAppH e es             = foldl AppH e es

parseExprsH1 :: ReadS [ExprH]
parseExprsH1 = \ inp ->
        [ (e:es,inp2)
        | (e,inp1)  <- parseExprH0 inp
        , (es,inp2) <- parseExprsH1 inp1
        ] ++
        [ ([], inp) ]

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
                     | isId c    = [span isId (c:cs)]
parseToken _         = []

---------------------------------------------

isId :: Char -> Bool
isId c = isAlphaNum c || c `elem` "+._-:"

---------------------------------------------


