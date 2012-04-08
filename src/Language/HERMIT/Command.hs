-- Command is the *untyped* command and control language for HERMIT.

module Language.HERMIT.Command
        ( Command(..)
        , parseCommand
        ) where

import Data.Char
import Control.Monad

data Command
        = HVar String                   -- variable names (refer to source code)
        | HLit String                   -- commands (to be looked up in Dictionary)
        | HApp Command Command          -- application
        deriving Show

-- Cheap and cheerful parser. Pretty hacky for now
parseCommand :: String -> Either String Command
parseCommand str =
        case parseExpr str of
          ((e,""):_) -> Right e
          _ -> Left $ "bad parse for: " ++ str

parseExpr0 :: ReadS Command
parseExpr0 = \ inp ->
        [ (HVar str,inp1)
        | (str,inp1) <- parseToken inp
        , all isAlpha str
        ] ++
        [ (HLit str,inp2)
        | ("#",inp1) <- parseToken inp
        , (str,inp2) <- parseToken inp1
        ] ++
        [ (e,inp3)
        | ("(",inp1) <- parseToken inp
        , (e,inp2) <- parseExpr inp1
        , (")",inp3) <- parseToken inp2
        ]
parseExpr :: ReadS Command
parseExpr = \ inp ->
        [ (foldl HApp e es,inp2)
        | (e,inp1) <- parseExpr0 inp
        , (es,inp2) <- parseExprs inp1
        ]

parseExprs :: ReadS [Command]
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


