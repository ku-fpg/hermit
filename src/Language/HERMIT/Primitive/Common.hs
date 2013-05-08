-- | Note: this module should NOT export externals. It is for common
--   transformations needed by the other primitive modules.
module Language.HERMIT.Primitive.Common
    ( -- * Utility Transformations
      -- ** Finding function calls.
      callT
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

import Language.HERMIT.Kure
import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.GHC
import Language.HERMIT.Monad

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------

-- | Lift GHC's collectArgs
callT :: TranslateH CoreExpr (CoreExpr, [CoreExpr])
callT = do
    e <- idR
    case e of
        Var {} -> return (e, [])
        App {} -> return (collectArgs e)
        _      -> fail "not an application or variable occurence."

callPredT :: (Id -> [CoreExpr] -> Bool) -> TranslateH CoreExpr (CoreExpr, [CoreExpr])
callPredT p = do
    call@(Var i, args) <- callT
    guardMsg (p i args) "predicate failed."
    return call

-- | Succeeds if we are looking at an application of given function
--   returning zero or more arguments to which it is applied.
callNameT :: TH.Name -> TranslateH CoreExpr (CoreExpr, [CoreExpr])
callNameT nm = setFailMsg ("callNameT: not a call to " ++ show nm) $
    callPredT (const . cmpTHName2Var nm)

-- | Succeeds if we are looking at a fully saturated function call.
callSaturatedT :: TranslateH CoreExpr (CoreExpr, [CoreExpr])
callSaturatedT = callPredT (\ i args -> idArity i == length args)
-- TODO: probably better to calculate arity based on Id's type, as
--       idArity is conservatively set to zero by default.

-- | Succeeds if we are looking at an application of given function
callNameG :: TH.Name -> TranslateH CoreExpr ()
callNameG nm = prefixFailMsg "callNameG failed: " $ callNameT nm >>= \_ -> constT (return ())

-- | Succeeds if we are looking at an application of a data constructor.
callDataConT :: TranslateH CoreExpr (DataCon, [Type], [CoreExpr])
callDataConT = prefixFailMsg "callDataConT failed:" $
    contextfreeT (return . exprIsConApp_maybe idUnfolding)
        >>= maybe (fail "not a datacon application.") return

-- | Succeeds if we are looking at an application of a named data constructor.
callDataConNameT :: TH.Name -> TranslateH CoreExpr (DataCon, [Type], [CoreExpr])
callDataConNameT nm = do
    res@(dc,_,_) <- callDataConT
    guardMsg (cmpTHName2Name nm (dataConName dc)) "wrong datacon."
    return res

-- | Apply a rewrite to all applications of a given function in a top-down manner, pruning on success.
callsR :: TH.Name -> RewriteH CoreExpr -> RewriteH Core
callsR nm rr = prunetdR (promoteExprR $ callNameG nm >> rr)

-- | Apply a translate to all applications of a given function in a top-down manner,
--   pruning on success, collecting the results.
callsT :: TH.Name -> TranslateH CoreExpr b -> TranslateH Core [b]
callsT nm t = collectPruneT (promoteExprT $ callNameG nm >> t)

------------------------------------------------------------------------------

-- | List all identifiers bound at the top-level in a program.
progIdsT :: TranslateH CoreProg [Id]
progIdsT = progNilT [] <+ progConsT bindVarsT progIdsT (++)

-- | List the identifiers bound by the top-level binding group at the head of the program.
consIdsT :: TranslateH CoreProg [Id]
consIdsT = progConsT bindVarsT mempty (\ vs () -> vs)

-- | List the identifiers bound by a recursive top-level binding group at the head of the program.
consRecIdsT :: TranslateH CoreProg [Id]
consRecIdsT = progConsT recIdsT mempty (\ vs () -> vs)

-- | Return the identifier bound by a non-recursive top-level binding at the head of the program.
consNonRecIdT :: TranslateH CoreProg Id
consNonRecIdT = progConsT nonRecVarT mempty (\ v () -> v)

-- | List all variables bound in a binding group.
bindVarsT :: TranslateH CoreBind [Var]
bindVarsT = fmap return nonRecVarT <+ recIdsT

-- | Return the variable bound by a non-recursive let expression.
nonRecVarT :: TranslateH CoreBind Var
nonRecVarT = nonRecT mempty (\ v () -> v)

-- | List all identifiers bound in a recursive binding group.
recIdsT :: TranslateH CoreBind [Id]
recIdsT = recT (\ _ -> defIdT) id

-- | Return the identifier bound by a recursive definition.
defIdT :: TranslateH CoreDef Id
defIdT = defT mempty (\ v () -> v)

-- | Return the variable bound by a lambda expression.
lamVarT :: TranslateH CoreExpr Var
lamVarT = lamT mempty (\ v () -> v)

-- | List the variables bound by a let expression.
letVarsT :: TranslateH CoreExpr [Var]
letVarsT = letT bindVarsT mempty (\ vs () -> vs)

-- | List the identifiers bound by a recursive let expression.
letRecIdsT :: TranslateH CoreExpr [Id]
letRecIdsT = letT recIdsT mempty (\ vs () -> vs)

-- | Return the variable bound by a non-recursive let expression.
letNonRecVarT :: TranslateH CoreExpr Var
letNonRecVarT = letT nonRecVarT mempty (\ v () -> v)

-- | List all variables bound by a case expression (in the alternatives and the wildcard binder).
caseVarsT :: TranslateH CoreExpr [Var]
caseVarsT = caseT mempty (\ _ -> altVarsT) (\ () v _ vss -> v : nub (concat vss))

-- | Return the case wildcard binder.
caseWildIdT :: TranslateH CoreExpr Id
caseWildIdT = caseT mempty (\ _ -> return ()) (\ () v _ _ -> v)

-- | List the variables bound by all alternatives in a case expression.
caseAltVarsT :: TranslateH CoreExpr [[Var]]
caseAltVarsT = caseT mempty (\ _ -> altVarsT) (\ () _ _ vss -> vss)

-- | List the variables bound by a case alternative.
altVarsT :: TranslateH CoreAlt [Var]
altVarsT = altT mempty (\ _ vs () -> vs)

------------------------------------------------------------------------------

-- Need a better error type so that we can factor out the repetition.

-- | Lifted version of 'boundVars'.
boundVarsT :: TranslateH a [Var]
boundVarsT = contextonlyT (return . boundVars)

-- | Find the unique variable bound in the context that matches the given name, failing if it is not unique.
findBoundVarT :: TH.Name -> TranslateH a Var
findBoundVarT nm = prefixFailMsg ("Cannot resolve name " ++ TH.nameBase nm ++ ", ") $
                        do c <- contextT
                           case findBoundVars nm c of
                             []         -> fail "no matching variables in scope."
                             [v]        -> return v
                             _ : _ : _  -> fail "multiple matching variables in scope."

-- | Lookup the name in the 'HermitC' first, then, failing that, in GHC's global reader environment.
findIdT :: TH.Name -> TranslateH a Id
findIdT nm = prefixFailMsg ("Cannot resolve name " ++ TH.nameBase nm ++ ", ") $
             contextonlyT (findId nm)

findId :: TH.Name -> HermitC -> HermitM Id
findId nm c = case findBoundVars nm c of
                []         -> findIdMG nm c
                [v]        -> return v
                _ : _ : _  -> fail "multiple matching variables in scope."

findIdMG :: TH.Name -> HermitC -> HermitM Id
findIdMG nm c =
    case filter isValName $ findNameFromTH (mg_rdr_env $ hermitModGuts c) nm of
      []  -> findIdBuiltIn nm
      [n] -> lookupId n
      ns  -> do dynFlags <- getDynFlags
                fail $ "multiple matches found:\n" ++ intercalate ", " (map (showPpr dynFlags) ns)

findIdBuiltIn :: TH.Name -> HermitM Id
findIdBuiltIn = go . TH.nameBase
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

          dataConId :: DataCon -> HermitM Id
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

