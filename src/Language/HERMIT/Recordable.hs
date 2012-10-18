module Recordable where

-- Experimental!
-- Warning: it's unclear how best to handle scoping.

import Data.Dynamic
import Data.Map

import Control.Arrow

import Language.HERMIT.Kure
import Language.HERMIT.Expr
import Language.HERMIT.External
import Language.HERMIT.Interp

------------------------------------

data Recordable = RecRewrite (RewriteH Core)
                | RecPath (TranslateH Core Path)
                | RecScope [Recordable]

------------------------------------

interpRecordable :: [Interp Recordable]
interpRecordable =
                [ interp (\ (RewriteCoreBox r)       -> RecRewrite r)
                , interp (\ (TranslateCorePathBox t) -> RecPath t)
                ]

------------------------------------

recordables2rewrite :: [Recordable] -> RewriteH Core
recordables2rewrite []            = idR
recordables2rewrite (rec : recs)  = let rest = recordables2rewrite recs
                                     in case rec of
                                          RecScope recs1 -> recordables2rewrite recs1 >>> rest
                                          RecRewrite r   -> r >>> rest
                                          RecPath t      -> do p <- t
                                                               pathR p rest

------------------------------------

type Dictionary = Map String [Dynamic]

recordStmts :: Dictionary -> [StmtH ExprH] -> Either String [Recordable]
recordStmts dict []                = Right []
recordStmts dict (ExprH e    : ss) = do rec <- recordExpr dict e
                                        recs  <- recordStmts dict ss
                                        Right (rec : recs)
recordStmts dict (ScopeH ss1 : ss) = do recs1 <- recordStmts dict ss1
                                        recs  <- recordStmts dict ss
                                        Right (RecScope recs1 : recs)

-- currently produces inappropriate error message
recordExpr :: Dictionary -> ExprH -> Either String Recordable
recordExpr dict exp = interpExprH dict interpRecordable exp

------------------------------------

stmts2rewrite :: Dictionary -> [StmtH ExprH] -> Either String (RewriteH Core)
stmts2rewrite dict stmts = recordables2rewrite `fmap` recordStmts dict stmts

-----------------------------------
