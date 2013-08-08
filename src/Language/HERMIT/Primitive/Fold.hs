module Language.HERMIT.Primitive.Fold
    ( -- * Fold/Unfold Transformation
      externals
    , foldR
    , foldVarR
    , stashFoldR
    , stashFoldAnyR
    )

where

import GhcPlugins hiding (empty)

import Control.Arrow
import Control.Applicative
import Control.Monad

import Data.List (intercalate)
import qualified Data.Map as Map

import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.Monad
import Language.HERMIT.Kure
import Language.HERMIT.External
import Language.HERMIT.GHC

import Language.HERMIT.Primitive.GHC hiding (externals)
import Language.HERMIT.Primitive.Inline hiding (externals)

import qualified Language.Haskell.TH as TH

import Prelude hiding (exp)

------------------------------------------------------------------------

externals :: [External]
externals =
    [ external "fold" (promoteExprR . foldR :: TH.Name -> RewriteH Core)
        [ "fold a definition"
        , ""
        , "double :: Int -> Int"
        , "double x = x + x"
        , ""
        , "5 + 5 + 6"
        , "any-bu (fold 'double)"
        , "double 5 + 6"
        , ""
        , "Note: due to associativity, if you wanted to fold 5 + 6 + 6, "
        , "you first need to apply an associativity rewrite." ]  .+ Context .+ Deep
    , external "fold" (promoteExprR . stashFoldR :: Label -> RewriteH Core)
        [ "Fold a remembered definition." ]                      .+ Context .+ Deep
    , external "fold-any" (promoteExprR stashFoldAnyR :: RewriteH Core)
        [ "Attempt to fold any of the remembered definitions." ] .+ Context .+ Deep
    ]

------------------------------------------------------------------------

stashFoldR :: ReadBindings c => Label -> Rewrite c HermitM CoreExpr
stashFoldR label = prefixFailMsg "Fold failed: " $
    translate $ \ c e -> do
        Def i rhs <- lookupDef label
        guardMsg (inScope c i) $ var2String i ++ " is not in scope.\n(A common cause of this error is trying to fold a recursive call while being in the body of a non-recursive definition.  This can be resolved by calling \"nonrec-to-rec\" on the non-recursive binding group.)"
        maybe (fail "no match.")
              return
              (fold i rhs e)

stashFoldAnyR :: ReadBindings c => Rewrite c HermitM CoreExpr
stashFoldAnyR = setFailMsg "Fold failed: no definitions could be folded." $
                catchesM =<< map stashFoldR <$> (Map.keys <$> constT getStash)

foldR :: ReadBindings c => TH.Name -> Rewrite c HermitM CoreExpr
foldR nm = prefixFailMsg "Fold failed: " $
           do c <- contextT
              case findBoundVars nm c of
                []  -> fail "cannot find name."
                [v] -> foldVarR v Nothing
                vs  -> fail $ "multiple names match: " ++ intercalate ", " (map var2String vs)

foldVarR :: ReadBindings c => Var -> Maybe BindingDepth -> Rewrite c HermitM CoreExpr
foldVarR v md =
             do e <- idR
                (rhs,_) <- getUnfoldingT scrutinee caseBinderOnly md <<< return v
                maybe (fail "no match.") return (fold v rhs e)
  where
    scrutinee      = False
    caseBinderOnly = False

------------------------------------------------------------------------

fold :: Id -> CoreExpr -> CoreExpr -> Maybe CoreExpr
fold i lam exp = do
    let (vs,body) = collectBinders lam
        -- return Nothing if not equal, so sequence will fail below
        checkEqual :: Maybe CoreExpr -> Maybe CoreExpr -> Maybe CoreExpr
        checkEqual m1 m2 = ifM (exprEqual <$> m1 <*> m2) m1 Nothing

    al <- foldMatch vs [] body exp

    let m = Map.fromListWith checkEqual [(k,Just v) | (k,v) <- al ]

    es <- sequence [ join (Map.lookup v m) | v <- vs ]
    return $ mkCoreApps (varToCoreExpr i) es

-- Note: Id in the concrete instance is first
-- (not the Id found in the definition we are trying to fold).
addAlpha :: Id -> Id -> [(Id,Id)] -> [(Id,Id)]
addAlpha rId lId alphas | rId == lId = alphas
                        | otherwise  = (rId,lId) : alphas

-- Note: return list can have duplicate keys, caller is responsible
-- for checking that dupes refer to same expression
foldMatch :: [Var]          -- ^ vars that can unify with anything
          -> [(Id,Id)]      -- ^ alpha equivalences, wherever there is binding
                            --   note: we depend on behavior of lookup here, so new entries
                            --         should always be added to the front of the list so
                            --         we don't have to explicity remove them when shadowing occurs
          -> CoreExpr       -- ^ pattern we are matching on
          -> CoreExpr       -- ^ expression we are checking
          -> Maybe [(Var,CoreExpr)] -- ^ mapping of vars to expressions, or failure
foldMatch vs as (Var i) e | i `elem` vs = return [(i,e)]
                          | otherwise   = case e of
                                            Var i' | maybe False (==i) (lookup i' as) -> return [(i,e)]
                                                   | i == i' -> return []
                                            _                -> Nothing
foldMatch _  _ (Lit l) (Lit l') | l == l' = return []
foldMatch vs as (App e a) (App e' a') = do
    x <- foldMatch vs as e e'
    y <- foldMatch vs as a a'
    return (x ++ y)
foldMatch vs as (Lam v e) (Lam v' e') = foldMatch (filter (/=v) vs) (addAlpha v' v as) e e'
foldMatch vs as (Let (NonRec v rhs) e) (Let (NonRec v' rhs') e') = do
    x <- foldMatch vs as rhs rhs'
    y <- foldMatch (filter (/=v) vs) (addAlpha v' v as) e e'
    return (x ++ y)
-- TODO: this depends on bindings being in the same order
foldMatch vs as (Let (Rec bnds) e) (Let (Rec bnds') e') | length bnds == length bnds' = do
    let vs' = filter (`notElem` map fst bnds) vs
        as' = foldr (uncurry addAlpha) as $ zip (map fst bnds) (map fst bnds')
        bmatch (_,rhs) (_,rhs') = foldMatch vs' as' rhs rhs'
    x <- zipWithM bmatch bnds bnds'
    y <- foldMatch vs' as' e e'
    return (concat x ++ y)
foldMatch vs as (Tick t e) (Tick t' e') | t == t' = foldMatch vs as e e'
foldMatch vs as (Case s b ty alts) (Case s' b' ty' alts')
  | length alts == length alts' = do
    t <- foldMatch vs as (Type ty) (Type ty')
    x <- foldMatch vs as s s'
    let as' = addAlpha b' b as
        vs' = filter (/=b) vs
        altMatch (ac, is, e) (ac', is', e') | ac == ac' =
            foldMatch (filter (`notElem` is) vs') (foldr (uncurry addAlpha) as' $ zip is' is) e e'
        altMatch _ _ = Nothing
    y <- zipWithM altMatch alts alts'
    return (x ++ t ++ concat y)
foldMatch vs as (Cast e c)   (Cast e' c')  | coreEqCoercion c c' = foldMatch vs as e e'
-- don't try to alpha type variables for now
foldMatch vs _  (Type t@(TyVarTy v)) e@(Type t') | v `elem` vs = return [(v,e)]
                                                 | eqType t t' = return []
                                                 | otherwise   = Nothing
foldMatch _ _   (Type t)     (Type t')     | eqType t t' = return []
foldMatch _ _   (Coercion c) (Coercion c') | coreEqCoercion c c' = return []
foldMatch _ _ _ _ = Nothing
