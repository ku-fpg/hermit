{-# LANGUAGE InstanceSigs, FlexibleInstances, FlexibleContexts #-}

-- | Note: this module should NOT export externals. It is for common
--   transformations needed by the other primitive modules.
module Language.HERMIT.Primitive.Common
    ( altFreeVarsT
    , bindings
    , bindingVarsT
    , caseAltVarsT
    , caseBinderVarT
    , caseAltVarsWithBinderT
    , letVarsT
    , wrongExprForm
    , findBoundVarT
    , findIdT
    )
where

import GhcPlugins

import Control.Arrow

import Data.List
import Data.Monoid

import Language.HERMIT.Kure
import Language.HERMIT.Core
import Language.HERMIT.Context
import Language.HERMIT.GHC

import Language.HERMIT.Primitive.GHC

import qualified Language.Haskell.TH as TH

------------------------------------------------------------------------------

class BindEnv a where
    bindings :: a -> [Id]

-- | All the identifiers bound in this binding group.
instance BindEnv CoreBind where
    bindings :: CoreBind -> [Id]
    bindings (NonRec b _) = [b]
    bindings (Rec bs)     = map fst bs

instance BindEnv CoreAlt where
    bindings :: CoreAlt -> [Id]
    bindings (_,vs,_) = vs

instance BindEnv CoreExpr where
    bindings :: CoreExpr -> [Id]
    bindings (Lam b _)          = [b]
    bindings (Let bs _)         = bindings bs
    bindings (Case _ sc _ alts) = sc : nub (concatMap bindings alts)
    bindings _                  = []

instance BindEnv CoreProg where
    bindings :: CoreProg -> [Id]
    bindings p = nub (concatMap bindings $ progToBinds p)

instance BindEnv CoreDef  where
    bindings :: CoreDef -> [Id]
    bindings (Def b _) = [b]

bindingVarsT :: TranslateH Core [Var]
bindingVarsT = translate $ \ c core -> case core of
          ModGutsCore _ -> fail "Cannot get binding vars at topmost level"
          ProgCore x    -> apply (promoteT ((arr bindings) :: TranslateH CoreProg [Var])) c x
          BindCore x    -> apply (promoteT ((arr bindings) :: TranslateH CoreBind [Var])) c x
          DefCore x     -> apply (promoteT ((arr bindings) :: TranslateH CoreDef [Var])) c x
          ExprCore x    -> apply (promoteT ((arr bindings) :: TranslateH CoreExpr [Var])) c x
          AltCore x     -> apply (promoteT ((arr bindings) :: TranslateH CoreAlt [Var])) c x

-- TODO.  Isn't there a better way to handle this ?
-- Although the work of this Translate is handled by bindingVarsT
-- This implementation fails for any expression that is not a Let.
-- This specific argument matching is required where it is used in Local/Let.hs and Local/Case.hs
letVarsT :: TranslateH CoreExpr [Var]
letVarsT = setFailMsg "Not a Let expression." $
           do Let bs _ <- idR
              return (bindings bs)

-- | List of the list of Ids bound by each case alternative
caseAltVarsT :: TranslateH CoreExpr [[Id]]
caseAltVarsT = caseT mempty (const (extractT bindingVarsT)) $ \ () _ _ vs -> vs

-- | List of the list of Ids bound by each case alternative, including the Case binder in each list
caseAltVarsWithBinderT :: TranslateH CoreExpr [[Id]]
caseAltVarsWithBinderT = caseT mempty (const (extractT bindingVarsT)) $ \ () v _ vs -> map (v:) vs

-- | list containing the single Id of the case binder
caseBinderVarT :: TranslateH CoreExpr [Id]
caseBinderVarT = setFailMsg "Not a Case expression." $
                 do Case _ b _ _ <- idR
                    return [b]

-- | Free variables for a CoreAlt, returns a function, which accepts
--   the coreBndr name, before giving a result.
--   This is so we can use this with congruence combinators:
--
--   caseT id (const altFreeVarsT) $ \ _ bndr _ fs -> [ f bndr | f <- fs ]
altFreeVarsT :: TranslateH CoreAlt (Id -> [Var])
altFreeVarsT = altT freeVarsT $ \ _con ids frees coreBndr -> nub frees \\ nub (coreBndr : ids)

------------------------------------------------------------------------------

-- | Constructs a common error message.
--   Argument 'String' should be the desired form of the expression.
wrongExprForm :: String -> String
wrongExprForm form = "Expression does not have the form: " ++ form

------------------------------------------------------------------------------

-- Need a better error type so that we can factor out the repetition.

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
