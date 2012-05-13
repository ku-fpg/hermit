-- Expr is the *untyped* command and control language for HERMIT.

module Language.HERMIT.Expr
        ( Expr(..)
        , parseExpr
        ) where

import Data.Char

---------------------------------------------

-- Our local version of Expr, for things parsed from string or JSON structures.
data Expr
        = Var String                   -- variable names (refer to source code)
        | Lit String                   -- commands (to be looked up in Dictionary)
        | App Expr Expr                -- application
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

parseExpr :: String -> Either String Expr
parseExpr = parse parseExpr1

parseExprs :: String -> Either String [Expr]
parseExprs = parse parseExprs'

---------------------------------------------

parseExprs' :: ReadS [Expr]
parseExprs' =
        parseExpr1 `bind` (\ a ->
        many (some (item ";") `bind` \ _ -> parseExpr1) `bind` (\ as ->
        (\ inp -> [(a:as,inp)])))

parseExpr0 :: ReadS Expr
parseExpr0 = \ inp ->
        [ (Var str,inp1)
        | (str,inp1) <- parseToken inp
        , all isId str
        ] ++
        [ (Lit str,inp2)
        | ("'",inp1) <- parseToken inp
        , (str,inp2) <- parseToken inp1
        ] ++
        [ (e,inp3)
        | ("(",inp1) <- parseToken inp
        , (e,inp2)   <- parseExpr1 inp1
        , (")",inp3) <- parseToken inp2
        ]
        
parseExpr1 :: ReadS Expr
parseExpr1 = \ inp ->
        [ (foldl App e es,inp2)
        | (e,inp1)  <- parseExpr0 inp
        , (es,inp2) <- parseExprs1 inp1
        ]

parseExprs1 :: ReadS [Expr]
parseExprs1 = \ inp ->
        [ (e:es,inp2)
        | (e,inp1)  <- parseExpr0 inp
        , (es,inp2) <- parseExprs1 inp1
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
parseToken (c   :cs) | isSpace c = parseToken cs
                     | isId c    = [span isId (c:cs)]
parseToken _         = []

---------------------------------------------

isId :: Char -> Bool
isId c = isAlphaNum c || c `elem` "._-:"
               
---------------------------------------------


