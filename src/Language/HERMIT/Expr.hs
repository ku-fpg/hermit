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
          ((e,""):_) -> Right e
          _ -> Left $ "bad parse for: " ++ str

parseExpr0 :: ReadS Expr
parseExpr0 = \ inp ->
        [ (Var str,inp1)
        | (str,inp1) <- parseToken inp
        , all isAlpha str
        ] ++
        [ (Lit str,inp2)
        | ("#",inp1) <- parseToken inp
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
        , (es,inp2) <- parseExprs inp1
        ]

parseExprs :: ReadS [Expr]
parseExprs = \ inp ->
        [ (e:es,inp2)
        | (e,inp1) <- parseExpr0 inp
        , (es,inp2) <- parseExprs inp1
        ] ++
        [ ([], inp) ]

item :: String -> ReadS ()
item str = \ inp ->
        [ ((),rest)
        | (tok,rest) <- parseToken inp
        , tok == str
        ]

parseToken :: ReadS String
parseToken = \ inp -> if null inp then [] else lex inp


