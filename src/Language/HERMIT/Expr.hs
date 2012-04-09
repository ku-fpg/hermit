-- Expr is the *untyped* command and control language for HERMIT.

module Language.HERMIT.Expr
        ( Expr(..)
        , parseExpr
        ) where

import Data.Char
import Control.Monad

-- Our local version of Expr, for things parsed from string or JSON structures.
data Expr
        = Var String                   -- variable names (refer to source code)
        | Lit String                   -- commands (to be looked up in Dictionary)
        | App Expr Expr                -- application
        deriving Show

-- Cheap and cheerful parser. Pretty hacky for now
parseExpr :: String -> Either String Expr
parseExpr str =
        case parseExpr1 str of
          ((e,str):_) | all isSpace str -> Right e
          _ -> Left $ "bad parse for: " ++ str

parseExprs :: String -> Either String [Expr]
parseExprs str =
        case parseExprs' str of
          ((e,str):_) | all isSpace str -> Right e
          _ -> Left $ "bad parse for: " ++ str

---------------------------------------------

parseExprs' :: ReadS [Expr]
parseExprs' =
        parseExpr1 `bind` (\ a ->
        many (some (item ";") `bind` \ _ -> parseExpr1) `bind` (\ as ->
        (\ inp -> [(a:as,inp)])))

bind :: ReadS a -> (a -> ReadS b) -> ReadS b
bind m k = \ inp ->
        [ (b,inp2)
        | (a,inp1) <- m inp
        , (b,inp2) <- k a inp1
        ]




many p = \ inp ->
     some p inp ++
     [ ([], inp) ]

some p = \ inp ->
     [ (x:xs,inp2)
     | (x,inp1)  <- p inp
     , (xs,inp2) <- many p inp1
     ]




parseExpr0 :: ReadS Expr
parseExpr0 = \ inp ->
        [ (Var str,inp1)
        | (str,inp1) <- parseToken inp
        , all isAlphaNum str
        ] ++
        [ (Lit str,inp2)
        | ("'",inp1) <- parseToken inp
        , (str,inp2) <- parseToken inp1
        ] ++
        [ (e,inp3)
        | ("(",inp1) <- parseToken inp
        , (e,inp2) <- parseExpr1 inp1
        , (")",inp3) <- parseToken inp2
        ]
parseExpr1 :: ReadS Expr
parseExpr1 = \ inp ->
        [ (foldl App e es,inp2)
        | (e,inp1) <- parseExpr0 inp
        , (es,inp2) <- parseExprs1 inp1
        ]

parseExprs1 :: ReadS [Expr]
parseExprs1 = \ inp ->
        [ (e:es,inp2)
        | (e,inp1) <- parseExpr0 inp
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
parseToken []       = []
parseToken ('\n':cs) = [(";",cs)]               -- yes, really
parseToken (c:cs)    | isSpace c = parseToken cs
parseToken ('(':cs) = [("(",cs)]
parseToken (')':cs) = [(")",cs)]
parseToken ('{':cs) = [("{",cs)]
parseToken ('}':cs) = [("}",cs)]
parseToken (';':cs) = [(";",cs)]
parseToken ('\'':cs) = [("'",cs)]
parseToken (c:cs)    | isAlphaNum c || c `elem` "._" = lex (c:cs)
parseToken _         = []



