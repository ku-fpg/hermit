{-# LANGUAGE CPP, ScopedTypeVariables, FlexibleContexts, LambdaCase #-}

-- | Note: this module should NOT export externals. It is for common
--   transformations needed by the other primitive modules.
module HERMIT.Dictionary.Common
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
      -- ** Collecting variable bindings
    , progConsIdsT
    , progConsRecIdsT
    , progConsNonRecIdT
    , nonRecVarT
    , recIdsT
    , lamVarT
    , letVarsT
    , letRecIdsT
    , letNonRecVarT
    , caseVarsT
    , caseBinderIdT
    , caseAltVarsT
      -- ** Finding variables bound in the Context
    , boundVarsT
    , findBoundVarT
    , findIdT
    , findId
    , varBindingDepthT
    , varIsOccurrenceOfT
    , exprIsOccurrenceOfT
    , inScope
    , withVarsInScope
      -- Miscellaneous
    , wrongExprForm
    )

where

import Data.List
import Data.Monoid

import Control.Arrow
import Control.Monad
import Control.Monad.IO.Class

import HERMIT.Context
import HERMIT.Core
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad
import HERMIT.Name

------------------------------------------------------------------------------

-- | Apply a transformation to a value in the current context.
applyInContextT :: Transform c m a b -> a -> Transform c m x b
applyInContextT t a = contextonlyT $ \ c -> apply t c a

-- Note: this is the same as: return a >>> t

------------------------------------------------------------------------------

-- | Lift GHC's collectArgs
callT :: Monad m => Transform c m CoreExpr (CoreExpr, [CoreExpr])
callT = contextfreeT $ \ e -> case e of
                                Var {} -> return (e, [])
                                App {} -> return (collectArgs e)
                                _      -> fail "not an application or variable occurence."

callPredT :: Monad m => (Id -> [CoreExpr] -> Bool) -> Transform c m CoreExpr (CoreExpr, [CoreExpr])
callPredT p = do
    call@(Var i, args) <- callT
    guardMsg (p i args) "predicate failed."
    return call

-- | Succeeds if we are looking at an application of given function
--   returning zero or more arguments to which it is applied.
callNameT :: MonadCatch m => String -> Transform c m CoreExpr (CoreExpr, [CoreExpr])
callNameT nm = setFailMsg ("callNameT failed: not a call to '" ++ nm ++ ".") $
    callPredT (const . cmpString2Var nm)

-- | Succeeds if we are looking at a fully saturated function call.
callSaturatedT :: Monad m => Transform c m CoreExpr (CoreExpr, [CoreExpr])
callSaturatedT = callPredT (\ i args -> idArity i == length args)
-- TODO: probably better to calculate arity based on Id's type, as
--       idArity is conservatively set to zero by default.

-- | Succeeds if we are looking at an application of given function
callNameG :: MonadCatch m => String -> Transform c m CoreExpr ()
callNameG nm = prefixFailMsg "callNameG failed: " $ callNameT nm >>= \_ -> constT (return ())

-- | Succeeds if we are looking at an application of a data constructor.
callDataConT :: MonadCatch m => Transform c m CoreExpr (DataCon, [Type], [CoreExpr])
callDataConT = prefixFailMsg "callDataConT failed:" $
#if __GLASGOW_HASKELL__ > 706
    do mb <- contextfreeT $ \ e -> let in_scope = mkInScopeSet (mkVarEnv [ (v,v) | v <- varSetElems (localFreeVarsExpr e) ])
                                   in return $ exprIsConApp_maybe (in_scope, idUnfolding) e
       maybe (fail "not a datacon application.") return mb
#else
    contextfreeT (return . exprIsConApp_maybe idUnfolding)
        >>= maybe (fail "not a datacon application.") return
#endif

-- | Succeeds if we are looking at an application of a named data constructor.
callDataConNameT :: MonadCatch m => String -> Transform c m CoreExpr (DataCon, [Type], [CoreExpr])
callDataConNameT nm = do
    res@(dc,_,_) <- callDataConT
    guardMsg (cmpString2Name nm (dataConName dc)) "wrong datacon."
    return res

-- TODO: Both callsR and callsT should be eliminated, now that we have callNameT
-- | Apply a rewrite to all applications of a given function in a top-down manner, pruning on success.
callsR :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m) => String -> Rewrite c m CoreExpr -> Rewrite c m Core
callsR nm rr = prunetdR (promoteExprR $ callNameG nm >> rr)

-- | Apply a translate to all applications of a given function in a top-down manner,
--   pruning on success, collecting the results.
callsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m) => String -> Transform c m CoreExpr b -> Transform c m Core [b]
callsT nm t = collectPruneT (promoteExprT $ callNameG nm >> t)

------------------------------------------------------------------------------

-- | List the identifiers bound by the top-level binding group at the head of the program.
progConsIdsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Transform c m CoreProg [Id]
progConsIdsT = progConsT (arr bindVars) mempty (\ vs () -> vs)

-- | List the identifiers bound by a recursive top-level binding group at the head of the program.
progConsRecIdsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m CoreProg [Id]
progConsRecIdsT = progConsT recIdsT mempty (\ vs () -> vs)

-- | Return the identifier bound by a non-recursive top-level binding at the head of the program.
progConsNonRecIdT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m CoreProg Id
progConsNonRecIdT = progConsT nonRecVarT mempty (\ v () -> v)

-- | Return the variable bound by a non-recursive let expression.
nonRecVarT :: (ExtendPath c Crumb, Monad m) => Transform c m CoreBind Var
nonRecVarT = nonRecT idR mempty (\ v () -> v)

-- | List all identifiers bound in a recursive binding group.
recIdsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m CoreBind [Id]
recIdsT = recT (\ _ -> arr defId) id

-- | Return the variable bound by a lambda expression.
lamVarT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m CoreExpr Var
lamVarT = lamT idR mempty (\ v () -> v)

-- | List the variables bound by a let expression.
letVarsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, MonadCatch m) => Transform c m CoreExpr [Var]
letVarsT = letT (arr bindVars) mempty (\ vs () -> vs)

-- | List the identifiers bound by a recursive let expression.
letRecIdsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m CoreExpr [Id]
letRecIdsT = letT recIdsT mempty (\ vs () -> vs)

-- | Return the variable bound by a non-recursive let expression.
letNonRecVarT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m CoreExpr Var
letNonRecVarT = letT nonRecVarT mempty (\ v () -> v)

-- | List all variables bound by a case expression (in the alternatives and the case binder).
caseVarsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m CoreExpr [Var]
caseVarsT = caseT mempty idR mempty (\ _ -> arr altVars) (\ () v () vss -> v : nub (concat vss))

-- | Return the case binder.
caseBinderIdT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m CoreExpr Id
caseBinderIdT = caseT mempty idR mempty (\ _ -> idR) (\ () i () _ -> i)

-- | List the variables bound by all alternatives in a case expression.
caseAltVarsT :: (ExtendPath c Crumb, ReadPath c Crumb, AddBindings c, Monad m) => Transform c m CoreExpr [[Var]]
caseAltVarsT = caseT mempty mempty mempty (\ _ -> arr altVars) (\ () () () vss -> vss)

------------------------------------------------------------------------------

-- | Find the depth of a variable's binding.
varBindingDepthT :: (ReadBindings c, Monad m) => Var -> Transform c m g BindingDepth
varBindingDepthT v = contextT >>= lookupHermitBindingDepth v

-- | Determine if the current variable matches the given variable, and is bound at the specified depth (helpful to detect shadowing).
varIsOccurrenceOfT :: (ExtendPath c Crumb, ReadBindings c, Monad m) => Var -> BindingDepth -> Transform c m Var Bool
varIsOccurrenceOfT v d = readerT $ \ v' -> if v == v'
                                             then varBindingDepthT v >>^ (== d)
                                             else return False

-- | Determine if the current expression is an occurrence of the given variable, bound at the specified depth (helpful to detect shadowing).
exprIsOccurrenceOfT :: (ExtendPath c Crumb, ReadBindings c, Monad m) => Var -> BindingDepth -> Transform c m CoreExpr Bool
exprIsOccurrenceOfT v d = varT $ varIsOccurrenceOfT v d

-- | Lifted version of 'boundVars'.
boundVarsT :: (BoundVars c, Monad m) => Transform c m a VarSet
boundVarsT = contextonlyT (return . boundVars)

-- | An instance of 'MonadThings' for 'Transform', which looks in the context first.
instance (MonadThings m, BoundVars c) => MonadThings (Transform c m a) where -- TODO: where to put this instance?
    lookupThing nm = contextonlyT $ \ c ->
                        case varSetElems $ filterVarSet ((== nm) . varName) (boundVars c) of
                            (i:_) -> return $ AnId i
                            []    -> lookupThing nm

-- | Find the unique variable bound in the context that matches the given name, failing if it is not unique.
findBoundVarT :: (BoundVars c, MonadCatch m) => String -> Transform c m a Var
findBoundVarT nm = prefixFailMsg ("Cannot resolve name " ++ nm ++ ", ") $
                        do c <- contextT
                           case varSetElems (findBoundVars nm c) of
                             []         -> fail "no matching variables in scope."
                             [v]        -> return v
                             _ : _ : _  -> fail "multiple matching variables in scope."

-- | Lookup the name in the context first, then, failing that, in GHC's global reader environment.
findIdT :: (BoundVars c, HasModGuts m, HasHscEnv m, MonadCatch m, MonadIO m, MonadThings m) => String -> Transform c m a Id
findIdT nm = prefixFailMsg ("Cannot resolve name " ++ nm ++ ", ") $
             contextonlyT (findId nm)

-- | Looks for Id with given name in the context. If it is not present, calls 'findIdMG'.
findId :: (BoundVars c, HasModGuts m, HasHscEnv m, MonadCatch m, MonadIO m, MonadThings m) => String -> c -> m Id
findId nm c = case varSetElems (findBoundVars nm c) of
                []         -> findIdMG (parseName nm) 
                [v]        -> return v
                _ : _ : _  -> fail "multiple matching variables in scope."

#if __GLASGOW_HASKELL__ > 706
-- | Looks for Id in current GlobalRdrEnv. If not present, calls 'findIdPackageDB'.
findIdMG :: (HasHscEnv m, HasModGuts m, MonadCatch m, MonadIO m, MonadThings m) => HermitName -> m Id
findIdMG nm = setFailMsg "variable not in scope." $ do
    rdrEnv <- liftM mg_rdr_env getModGuts
    catchesM [ case lookupGRE_RdrName (toRdrName ns nm) rdrEnv of
                [gre] -> nameToId $ gre_name gre
                []    -> findIdPackageDB ns nm
                _     -> fail "findIdMG: multiple names returned"
             | ns <- [varNS, dataConNS]
             ]

-- | Looks for Id in package database, or built-in packages.
findIdPackageDB :: (HasHscEnv m, HasModGuts m, MonadIO m, MonadThings m) => NameSpace -> HermitName -> m Id
findIdPackageDB ns nm = do
    mnm <- lookupName ns nm
    case mnm of
        Nothing -> findIdBuiltIn (hnUnqualified nm)
        Just n  -> nameToId n
#else
findIdMG :: (HasModGuts m, MonadThings m) => HermitName -> m Id
findIdMG hnm = do
    let nm = hnUnqualified hnm
    rdrEnv <- liftM mg_rdr_env getModGuts
    case filter isValName $ findNamesFromString rdrEnv nm of
        []  -> findIdBuiltIn nm
        [n] -> nameToId n
        ns  -> fail $ "multiple matches found:\n" ++ intercalate ", " (map getOccString ns)
#endif

-- | We have a name, find the corresponding Id.
nameToId :: MonadThings m => Name -> m Id
nameToId n | isVarName n     = lookupId n
           | isDataConName n = liftM dataConWrapId $ lookupDataCon n
           | otherwise       = fail "nameToId: unknown name type"

findIdBuiltIn :: forall m. Monad m => String -> m Id
findIdBuiltIn = go
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


-- TODO: "inScope" was defined elsewhere, but I've moved it here.  Should it be combined with the above functions?

-- | Determine whether a variable is in scope.
inScope :: ReadBindings c => c -> Var -> Bool
inScope c v = (v `boundIn` c) ||                 -- defined in this module
              (isId v &&                         -- idInfo panics on TyVars
               case unfoldingInfo (idInfo v) of
                CoreUnfolding {} -> True         -- defined elsewhere
                DFunUnfolding {} -> True
                _                -> False)

-- | Modify transformation to apply to current expression as if it were the body of a lambda binding the given variables.
withVarsInScope :: forall c m b. (ReadPath c Crumb, ExtendPath c Crumb, AddBindings c, HasEmptyContext c, MonadCatch m)
                => [Var] -> Transform c m CoreExpr b -> Transform c m CoreExpr b
withVarsInScope vs t = arr (mkCoreLams vs) >>> extractT (pathT (replicate (length vs) Lam_Body) (promoteExprT t :: Transform c m Core b))

------------------------------------------------------------------------------

-- | Constructs a common error message.
--   Argument 'String' should be the desired form of the expression.
wrongExprForm :: String -> String
wrongExprForm form = "Expression does not have the form: " ++ form

------------------------------------------------------------------------------
