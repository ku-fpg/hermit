-- | Note: this module should NOT export externals. It is for common
--   transformations needed by the other primitive modules.
module Language.HERMIT.Primitive.Common
    ( -- * Utility Transformations
      -- ** Collecting variables bound at a Node
      progVarsT
    , bindVarsT
    , nonRecVarT
    , recVarsT
    , defVarT
    , lamVarT
    , letVarsT
    , letRecVarsT
    , letNonRecVarT
    , caseVarsT
    , caseWildVarT
    , caseAltVarsT
    , altVarsT
      -- ** Finding variables bound in the Context
    , boundVarsT
    , findBoundVarT
    , findIdT
      -- ** Error Message Generators
    , wrongExprForm
    )

where

import GhcPlugins

import Data.List
import Data.Monoid

import Language.HERMIT.Kure
import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.GHC

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------

-- | List all identifiers bound at the top-level in a program.
progVarsT :: TranslateH CoreProg [Id]
progVarsT = progNilT [] <+ progConsT bindVarsT progVarsT (++)

-- | List all identifiers bound in a binding group.
bindVarsT :: TranslateH CoreBind [Var]
bindVarsT = fmap return nonRecVarT <+ recVarsT

-- | Return the variable bound by a non-recursive let expression.
nonRecVarT :: TranslateH CoreBind Var
nonRecVarT = nonRecT mempty (\ v () -> v)

-- | List all identifiers bound in a recursive binding group.
recVarsT :: TranslateH CoreBind [Id]
recVarsT = recT (\ _ -> defVarT) id

-- | Return the identifier bound by a recursive definition.
defVarT :: TranslateH CoreDef Id
defVarT = defT mempty (\ v () -> v)

-- | Return the variable bound by a lambda expression.
lamVarT :: TranslateH CoreExpr Var
lamVarT = lamT mempty (\ v () -> v)

-- | List the variables bound by a let expression.
letVarsT :: TranslateH CoreExpr [Var]
letVarsT = letT bindVarsT mempty (\ vs () -> vs)

-- | List the variables bound by a recursive let expression.
letRecVarsT :: TranslateH CoreExpr [Var]
letRecVarsT = letT recVarsT mempty (\ vs () -> vs)

-- | Return the variable bound by a non-recursive let expression.
letNonRecVarT :: TranslateH CoreExpr Var
letNonRecVarT = letT nonRecVarT mempty (\ v () -> v)

-- | List all variables bound by a case expression (in the alternatives and the wildcard binder).
caseVarsT :: TranslateH CoreExpr [Var]
caseVarsT = caseT mempty (\ _ -> altVarsT) (\ () v _ vss -> v : nub (concat vss))

-- | Return the case wildcard binder.
caseWildVarT :: TranslateH CoreExpr Var
caseWildVarT = caseT mempty (\ _ -> return ()) (\ () v _ _ -> v)

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
             do c <- contextT
                case findBoundVars nm c of
                  []         -> findIdMG nm
                  [v]        -> return v
                  _ : _ : _  -> fail "multiple matching variables in scope."

findIdMG :: TH.Name -> TranslateH a Id
findIdMG nm = contextonlyT $ \ c ->
    case filter isValName $ findNameFromTH (mg_rdr_env $ hermitModGuts c) nm of
      []  -> fail $ "variable not in scope."
      [n] -> lookupId n
      ns  -> do dynFlags <- getDynFlags
                fail $ "multiple matches found:\n" ++ intercalate ", " (map (showPpr dynFlags) ns)

------------------------------------------------------------------------------

-- | Constructs a common error message.
--   Argument 'String' should be the desired form of the expression.
wrongExprForm :: String -> String
wrongExprForm form = "Expression does not have the form: " ++ form

------------------------------------------------------------------------------
