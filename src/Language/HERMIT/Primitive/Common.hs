{-# LANGUAGE CPP, ScopedTypeVariables, FlexibleContexts #-}

-- | Note: this module should NOT export externals. It is for common
--   transformations needed by the other primitive modules.
module Language.HERMIT.Primitive.Common
    ( -- * Utility Transformations
      applyInContextT
      -- ** Finding function calls.
    , callT
    , callPredT
    , callNameT
    , callSaturatedT
    , callNameG
    , callDataConT
    , callDataConNameT
    , callsR
    , callsT
      -- ** Collecting variables bound at a Node
    , progIdsT
    , consIdsT
    , consRecIdsT
    , consNonRecIdT
    , bindVarsT
    , nonRecVarT
    , recIdsT
    , defIdT
    , lamVarT
    , letVarsT
    , letRecIdsT
    , letNonRecVarT
    , caseVarsT
    , caseWildIdT
    , caseAltVarsT
    , altVarsT
      -- ** Finding variables bound in the Context
    , boundVarsT
    , findBoundVarT
    , findIdT
    , findId
      -- ** Miscallaneous
    , wrongExprForm
    , nodups
    , mapAlts
    )

where

import GhcPlugins

import Data.List
import Data.Monoid
import qualified Data.Set as S

import Control.Monad(liftM)

import Language.HERMIT.Kure
import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.GHC

import Language.HERMIT.Primitive.GHC

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax (showName)

------------------------------------------------------------------------------

-- | Apply a transformation to a value in the current context.
applyInContextT :: Translate c m a b -> a -> Translate c m x b
applyInContextT t a = contextonlyT $ \ c -> apply t c a

-- Note: this is the same as: return a >>> t

------------------------------------------------------------------------------

-- | Lift GHC's collectArgs
callT :: Monad m => Translate c m CoreExpr (CoreExpr, [CoreExpr])
callT = contextfreeT $ \ e -> case e of
                                Var {} -> return (e, [])
                                App {} -> return (collectArgs e)
                                _      -> fail "not an application or variable occurence."

callPredT :: Monad m => (Id -> [CoreExpr] -> Bool) -> Translate c m CoreExpr (CoreExpr, [CoreExpr])
callPredT p = do
    call@(Var i, args) <- callT
    guardMsg (p i args) "predicate failed."
    return call

-- | Succeeds if we are looking at an application of given function
--   returning zero or more arguments to which it is applied.
callNameT :: MonadCatch m => TH.Name -> Translate c m CoreExpr (CoreExpr, [CoreExpr])
callNameT nm = setFailMsg ("callNameT: not a call to " ++ show nm) $
    callPredT (const . cmpTHName2Var nm)

-- | Succeeds if we are looking at a fully saturated function call.
callSaturatedT :: Monad m => Translate c m CoreExpr (CoreExpr, [CoreExpr])
callSaturatedT = callPredT (\ i args -> idArity i == length args)
-- TODO: probably better to calculate arity based on Id's type, as
--       idArity is conservatively set to zero by default.

-- | Succeeds if we are looking at an application of given function
callNameG :: MonadCatch m => TH.Name -> Translate c m CoreExpr ()
callNameG nm = prefixFailMsg "callNameG failed: " $ callNameT nm >>= \_ -> constT (return ())

-- | Succeeds if we are looking at an application of a data constructor.
callDataConT :: MonadCatch m => Translate c m CoreExpr (DataCon, [Type], [CoreExpr])
callDataConT = prefixFailMsg "callDataConT failed:" $
#if __GLASGOW_HASKELL__ > 706
    do mb <- contextfreeT $ \ e -> let in_scope = mkInScopeSet (mkVarEnv [ (v,v) | v <- S.toList (coreExprFreeVars e) ])
                                   in return $ exprIsConApp_maybe (in_scope, idUnfolding) e
       maybe (fail "not a datacon application.") return mb
#else
    contextfreeT (return . exprIsConApp_maybe idUnfolding)
        >>= maybe (fail "not a datacon application.") return
#endif

-- | Succeeds if we are looking at an application of a named data constructor.
callDataConNameT :: MonadCatch m => TH.Name -> Translate c m CoreExpr (DataCon, [Type], [CoreExpr])
callDataConNameT nm = do
    res@(dc,_,_) <- callDataConT
    guardMsg (cmpTHName2Name nm (dataConName dc)) "wrong datacon."
    return res

-- | Apply a rewrite to all applications of a given function in a top-down manner, pruning on success.
callsR :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => TH.Name -> Rewrite c m CoreExpr -> Rewrite c m Core
callsR nm rr = prunetdR (promoteExprR $ callNameG nm >> rr)

-- | Apply a translate to all applications of a given function in a top-down manner,
--   pruning on success, collecting the results.
callsT :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => TH.Name -> Translate c m CoreExpr b -> Translate c m Core [b]
callsT nm t = collectPruneT (promoteExprT $ callNameG nm >> t)

------------------------------------------------------------------------------

-- | List all identifiers bound at the top-level in a program.
progIdsT :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Translate c m CoreProg [Id]
progIdsT = progNilT [] <+ progConsT bindVarsT progIdsT (++)

-- | List the identifiers bound by the top-level binding group at the head of the program.
consIdsT :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Translate c m CoreProg [Id]
consIdsT = progConsT bindVarsT mempty (\ vs () -> vs)

-- | List the identifiers bound by a recursive top-level binding group at the head of the program.
consRecIdsT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreProg [Id]
consRecIdsT = progConsT recIdsT mempty (\ vs () -> vs)

-- | Return the identifier bound by a non-recursive top-level binding at the head of the program.
consNonRecIdT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreProg Id
consNonRecIdT = progConsT nonRecVarT mempty (\ v () -> v)

-- | List all variables bound in a binding group.
bindVarsT :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Translate c m CoreBind [Var]
bindVarsT = liftM return nonRecVarT <+ recIdsT

-- | Return the variable bound by a non-recursive let expression.
nonRecVarT :: (ExtendPath c Crumb, Monad m) => Translate c m CoreBind Var
nonRecVarT = nonRecT idR mempty (\ v () -> v)

-- | List all identifiers bound in a recursive binding group.
recIdsT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreBind [Id]
recIdsT = recT (\ _ -> defIdT) id

-- | Return the identifier bound by a recursive definition.
defIdT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreDef Id
defIdT = defT idR mempty (\ v () -> v)

-- | Return the variable bound by a lambda expression.
lamVarT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreExpr Var
lamVarT = lamT idR mempty (\ v () -> v)

-- | List the variables bound by a let expression.
letVarsT :: (ExtendPath c Crumb, AddBindings c, MonadCatch m) => Translate c m CoreExpr [Var]
letVarsT = letT bindVarsT mempty (\ vs () -> vs)

-- | List the identifiers bound by a recursive let expression.
letRecIdsT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreExpr [Id]
letRecIdsT = letT recIdsT mempty (\ vs () -> vs)

-- | Return the variable bound by a non-recursive let expression.
letNonRecVarT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreExpr Var
letNonRecVarT = letT nonRecVarT mempty (\ v () -> v)

-- | List all variables bound by a case expression (in the alternatives and the wildcard binder).
caseVarsT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreExpr [Var]
caseVarsT = caseT mempty idR mempty (\ _ -> altVarsT) (\ () v () vss -> v : nub (concat vss))

-- | Return the case wildcard binder.
caseWildIdT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreExpr Id
caseWildIdT = caseT mempty idR mempty (\ _ -> idR) (\ () i () _ -> i)

-- | List the variables bound by all alternatives in a case expression.
caseAltVarsT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreExpr [[Var]]
caseAltVarsT = caseT mempty mempty mempty (\ _ -> altVarsT) (\ () () () vss -> vss)

-- | List the variables bound by a case alternative.
altVarsT :: (ExtendPath c Crumb, AddBindings c, Monad m) => Translate c m CoreAlt [Var]
altVarsT = altT mempty (\ _ -> idR) mempty (\ () vs () -> vs)

------------------------------------------------------------------------------

-- Need a better error type so that we can factor out the repetition.

-- | Lifted version of 'boundVars'.
boundVarsT :: (BoundVars c, Monad m) => Translate c m a (S.Set Var)
boundVarsT = contextonlyT (return . boundVars)

-- | Find the unique variable bound in the context that matches the given name, failing if it is not unique.
findBoundVarT :: (BoundVars c, MonadCatch m) => TH.Name -> Translate c m a Var
findBoundVarT nm = prefixFailMsg ("Cannot resolve name " ++ showName nm ++ ", ") $
                        do c <- contextT
                           case findBoundVars nm c of
                             []         -> fail "no matching variables in scope."
                             [v]        -> return v
                             _ : _ : _  -> fail "multiple matching variables in scope."

-- | Lookup the name in the context first, then, failing that, in GHC's global reader environment.
findIdT :: (BoundVars c, HasGlobalRdrEnv c, HasDynFlags m, MonadThings m, MonadCatch m) => TH.Name -> Translate c m a Id
findIdT nm = prefixFailMsg ("Cannot resolve name " ++ showName nm ++ ", ") $
             contextonlyT (findId nm)

findId :: (BoundVars c, HasGlobalRdrEnv c, HasDynFlags m, MonadThings m) => TH.Name -> c -> m Id
findId nm c = case findBoundVars nm c of
                []         -> findIdMG nm c
                [v]        -> return v
                _ : _ : _  -> fail "multiple matching variables in scope."

findIdMG :: (BoundVars c, HasGlobalRdrEnv c, HasDynFlags m, MonadThings m) => TH.Name -> c -> m Id
findIdMG nm c =
    case filter isValName $ findNamesFromTH (hermitGlobalRdrEnv c) nm of
      []  -> findIdBuiltIn nm
      [n] -> lookupId n
      ns  -> do dynFlags <- getDynFlags
                fail $ "multiple matches found:\n" ++ intercalate ", " (map (showPpr dynFlags) ns)

findIdBuiltIn :: forall m. Monad m => TH.Name -> m Id
findIdBuiltIn = go . showName
    where go ":"     = dataConId consDataCon
          go "[]"    = dataConId nilDataCon

          go "True"  = return trueDataConId
          go "False" = return falseDataConId

          go "<"     = return ltDataConId
          go "=="    = return eqDataConId
          go ">"     = return gtDataConId

          go "I#"    = dataConId intDataCon

          go "()"    = return unitDataConId
          -- TODO: add more as needed
          --       http://www.haskell.org/ghc/docs/latest/html/libraries/ghc/TysWiredIn.html
          go _   = fail "variable not in scope."

          dataConId :: DataCon -> m Id
          dataConId = return . dataConWorkId

------------------------------------------------------------------------------

-- | Constructs a common error message.
--   Argument 'String' should be the desired form of the expression.
wrongExprForm :: String -> String
wrongExprForm form = "Expression does not have the form: " ++ form

------------------------------------------------------------------------------

-- | Determine if a list contains no duplicated elements.
nodups :: Eq a => [a] -> Bool
nodups as = length as == length (nub as)

------------------------------------------------------------------------------

mapAlts :: (CoreExpr -> CoreExpr) -> [CoreAlt] -> [CoreAlt]
mapAlts f alts = [ (ac, vs, f e) | (ac, vs, e) <- alts ]

------------------------------------------------------------------------------
