{-# LANGUAGE ScopedTypeVariables, TypeFamilies, FlexibleContexts, TupleSections #-}
module Language.HERMIT.Primitive.Fold where

import GhcPlugins hiding (empty)

import Control.Applicative
import Control.Monad

import qualified Data.Map as Map

import Language.HERMIT.Monad
import Language.HERMIT.Context
import Language.HERMIT.External
import Language.HERMIT.Kure
import Language.HERMIT.GHC

import Language.HERMIT.Primitive.GHC
import Language.HERMIT.Primitive.Unfold

import qualified Language.Haskell.TH as TH

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: [External]
externals =
         [ external "fold" (promoteExprR . foldR)
                ["fold a definition"
                ,""
                ,"double :: Int -> Int"
                ,"double x = x + x"
                ,""
                ,"5 + 5 + 6"
                ,"any-bu (fold 'double)"
                ,"double 5 + 6"
                ,""
                ,"Note: due to associativity, if you wanted to fold 5 + 6 + 6, "
                ,"you first need to apply an associativity rewrite."
                ] .+ Context .+ Deep
         , external "stash-fold" (promoteExprR . stashFoldR)
                ["Fold a stashed definition."] .+ Context .+ Deep
         ]

------------------------------------------------------------------------

stashFoldR :: String -> RewriteH CoreExpr
stashFoldR label = prefixFailMsg "Fold failed: " $
                   contextfreeT $ \ e -> do
    Def i rhs <- lookupDef label
    maybe (fail "no match.")
          return
          (fold i rhs e)

foldR :: TH.Name -> RewriteH CoreExpr
foldR nm =  prefixFailMsg "Fold failed: " $
    translate $ \ c e -> do
        i <- case filter (\i -> nm `cmpTHName2Id` i) $ Map.keys (hermitBindings c) of
                [i] -> return i
                _ -> fail "cannot find name."
        either fail
               (\(rhs,_d) -> maybe (fail "no match.")
                                   return
                                   (fold i rhs e))
               (getUnfolding False False i c)

fold :: Id -> CoreExpr -> CoreExpr -> Maybe CoreExpr
fold i lam exp = do
    let (vs,body) = foldArgs lam
        -- return Nothing if not equal, so sequence will fail below
        checkEqual :: Maybe CoreExpr -> Maybe CoreExpr -> Maybe CoreExpr
        checkEqual m1 m2 = condM (exprEqual <$> m1 <*> m2) m1 Nothing

    al <- foldMatch vs body exp

    let m = Map.fromListWith checkEqual [(k,Just v) | (k,v) <- al ]

    es <- sequence [ join (Map.lookup v m) | v <- vs ]
    return $ mkCoreApps (Var i) es

-- | Collect arguments to function we are folding, so we can unify with them.
foldArgs :: CoreExpr -> ([Var], CoreExpr)
foldArgs = go []
    where go vs (Lam v e) = go (v:vs) e
          go vs e         = (reverse vs, e)

-- Note: return list can have duplicate keys, caller is responsible
-- for checking that dupes refer to same expression
foldMatch :: [Var]          -- ^ vars that can unify with anything
          -> CoreExpr       -- ^ pattern we are matching on
          -> CoreExpr       -- ^ expression we are checking
          -> Maybe [(Var,CoreExpr)] -- ^ mapping of vars to expressions, or failure
foldMatch vs (Var i) e | i `elem` vs = return [(i,e)]
                       | otherwise   = case e of
                                         Var i' | i == i' -> return []
                                         _                -> Nothing
foldMatch _  (Lit l) (Lit l') | l == l' = return []
foldMatch vs (App e a) (App e' a') = do
    x <- foldMatch vs e e'
    y <- foldMatch vs a a'
    return (x ++ y)
foldMatch vs (Lam v e) (Lam v' e') | v == v' = foldMatch (filter (==v) vs) e e'
foldMatch vs (Let (NonRec v rhs) e) (Let (NonRec v' rhs') e') | v == v' = do
    x <- foldMatch vs rhs rhs'
    y <- foldMatch (filter (==v) vs) e e'
    return (x ++ y)
foldMatch vs (Let (Rec bnds) e) (Let (Rec bnds') e') | length bnds == length bnds' = do
    let vs' = filter (`elem` map fst bnds) vs
        bmatch (v,rhs) (v',rhs') | v == v' = foldMatch vs' rhs rhs'
        bmatch _ _ = Nothing
    x <- zipWithM bmatch bnds bnds'
    y <- foldMatch vs' e e'
    return (concat x ++ y)
foldMatch vs (Tick t e) (Tick t' e') | t == t' = foldMatch vs e e'
-- TODO: showPpr hack in the rest of these!
-- TODO: we don't care if b == b' if they are not used anywhere
foldMatch vs (Case s b ty alts) (Case s' b' ty' alts')
  | (b == b') && (showPpr ty == showPpr ty') && (length alts == length alts') = do
    x <- foldMatch vs s s'
    let vs' = filter (==b) vs
        altMatch (ac, is, e) (ac', is', e') | (ac == ac') && (is == is') =
            foldMatch (filter (`elem` is) vs') e e'
        altMatch _ _ = Nothing
    y <- zipWithM altMatch alts alts'
    return (x ++ concat y)
foldMatch vs (Cast e c) (Cast e' c') | showPpr c == showPpr c' = foldMatch vs e e'
foldMatch _ (Type t) (Type t') | showPpr t == showPpr t' = return []
foldMatch _ (Coercion c) (Coercion c') | showPpr c == showPpr c' = return []
foldMatch _ _ _ = Nothing
