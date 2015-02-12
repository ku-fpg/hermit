{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, FlexibleInstances, TypeFamilies #-}
module HERMIT.Dictionary.Rules
    ( -- * GHC Rewrite Rules and Specialisation
      externals
      -- ** Rules
    , RuleName(..)
    , RuleNameListBox(..)
    , ruleR
    , rulesR
    , ruleToEqualityT
    , ruleNameToEqualityT
    , getHermitRuleT
    , getHermitRulesT
      -- ** Specialisation
    , specConstrR
    , specialiseR
    ) where

import qualified SpecConstr
import qualified Specialise

import Control.Arrow
import Control.Monad

import Data.Dynamic (Typeable)
import Data.Function (on)
import Data.List (deleteFirstsBy,intercalate)
import Data.String (IsString(..))

import HERMIT.Context
import HERMIT.Core
import HERMIT.Equality
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Monad

import HERMIT.Dictionary.GHC (dynFlagsT)
import HERMIT.Dictionary.Kure (anyCallR)
import HERMIT.Dictionary.Reasoning hiding (externals)
import HERMIT.Dictionary.Unfold (betaReducePlusR)

import IOEnv hiding (liftIO)

------------------------------------------------------------------------

-- | Externals dealing with GHC rewrite rules.
externals :: [External]
externals =
    [ external "rule-help" (rulesHelpListT :: TransformH CoreTC String)
        [ "List all the rules in scope." ] .+ Query
    , external "rule-help" (ruleHelpT :: RuleName -> TransformH CoreTC String)
        [ "Display details on the named rule." ] .+ Query
    , external "apply-rule" (promoteExprR . ruleR :: RuleName -> RewriteH Core)
        [ "Apply a named GHC rule" ] .+ Shallow
    , external "apply-rules" (promoteExprR . rulesR :: [RuleName] -> RewriteH Core)
        [ "Apply named GHC rules, succeed if any of the rules succeed" ] .+ Shallow
    , external "unfold-rule" ((\ nm -> promoteExprR (ruleR nm >>> tryR betaReducePlusR)) :: RuleName -> RewriteH Core)
        [ "Unfold a named GHC rule" ] .+ Deep .+ Context .+ TODO -- TODO: does not work with rules with no arguments
    , external "rule-to-lemma" (\nm -> do eq <- ruleNameToEqualityT nm
                                          insertLemmaT (fromString (show nm)) $ Lemma eq False False :: TransformH Core ())
        [ "Create a lemma from a GHC RULE." ]
    , external "spec-constr" (promoteModGutsR specConstrR :: RewriteH Core)
        [ "Run GHC's SpecConstr pass, which performs call pattern specialization."] .+ Deep
    , external "specialise" (promoteModGutsR specialiseR :: RewriteH Core)
        [ "Run GHC's specialisation pass, which performs type and dictionary specialisation."] .+ Deep
    ]

------------------------------------------------------------------------

newtype RuleName = RuleName String deriving (Eq, Typeable)

instance Extern RuleName where
    type Box RuleName = RuleName
    box = id
    unbox = id

instance IsString RuleName where fromString = RuleName
instance Show RuleName where show (RuleName s) = s

newtype RuleNameListBox = RuleNameListBox [RuleName] deriving Typeable

instance Extern [RuleName] where
    type Box [RuleName] = RuleNameListBox
    box = RuleNameListBox
    unbox (RuleNameListBox l) = l

-- | Lookup a rule by name, attempt to apply it. If successful, record it as an unproven lemma.
ruleR :: ( AddBindings c, ExtendPath c Crumb, HasCoreRules c, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
         , HasDynFlags m, HasHermitMEnv m, HasLemmas m, LiftCoreM m, MonadCatch m, MonadIO m, MonadThings m, MonadUnique m )
      => RuleName -> Rewrite c m CoreExpr
ruleR nm = do
    eq <- ruleNameToEqualityT nm
    forwardT (birewrite eq) >>> (constT (addLemma (fromString (show nm)) $ Lemma eq False True) >> idR)

rulesR :: ( AddBindings c, ExtendPath c Crumb, HasCoreRules c, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
          , HasDynFlags m, HasHermitMEnv m, HasLemmas m, LiftCoreM m, MonadCatch m, MonadIO m, MonadThings m, MonadUnique m )
       => [RuleName] -> Rewrite c m CoreExpr
rulesR = orR . map ruleR

-- | Return all in-scope CoreRules (including specialization RULES on binders), with their names.
getHermitRulesT :: (HasCoreRules c, HasHermitMEnv m, LiftCoreM m, MonadIO m) => Transform c m a [(RuleName, CoreRule)]
getHermitRulesT = contextonlyT $ \ c -> do
    rb      <- liftCoreM getRuleBase
    mgRules <- liftM mg_rules getModGuts
    hscEnv  <- liftCoreM getHscEnv
    rb'     <- liftM eps_rule_base $ liftIO $ runIOEnv () $ readMutVar (hsc_EPS hscEnv)
    let allRules = hermitCoreRules c ++ mgRules ++ concat (nameEnvElts rb) ++ concat (nameEnvElts rb')
    return [ (fromString (unpackFS (ruleName r)), r) | r <- allRules ]

-- | Get a GHC CoreRule by name.
getHermitRuleT :: (HasCoreRules c, HasHermitMEnv m, LiftCoreM m, MonadIO m) => RuleName -> Transform c m a CoreRule
getHermitRuleT name =
  do rulesEnv <- getHermitRulesT
     case filter ((name ==) . fst) rulesEnv of
       []      -> fail $ "failed to find rule: " ++ show name ++ ". If you think the rule exists, "
                         ++ "try running the flatten-module command at the top level."
       [(_,r)] -> return r
       _       -> fail ("Rule name \"" ++ show name ++ "\" is ambiguous.")

-- | List names of all CoreRules in scope.
rulesHelpListT :: (HasCoreRules c, HasHermitMEnv m, LiftCoreM m, MonadIO m) => Transform c m a String
rulesHelpListT = do
    rulesEnv <- getHermitRulesT
    return (intercalate "\n" $ reverse $ map (show.fst) rulesEnv)

-- | Print a named CoreRule using GHC's pretty printer for rewrite rules.
-- TODO: use our own Equality pretty printer.
ruleHelpT :: (HasCoreRules c, HasDynFlags m, HasHermitMEnv m, LiftCoreM m, MonadIO m)
          => RuleName -> Transform c m a String
ruleHelpT nm = do
    r <- getHermitRuleT nm
    dflags <- dynFlagsT
    return $ showSDoc dflags $ pprRulesForUser [r]

-- | Build an Equality from a named GHC rewrite rule.
ruleNameToEqualityT :: ( BoundVars c, HasCoreRules c, HasDynFlags m, HasHermitMEnv m
                       , LiftCoreM m, MonadCatch m, MonadIO m, MonadThings m )
                    => RuleName -> Transform c m a Equality
ruleNameToEqualityT name = getHermitRuleT name >>> ruleToEqualityT

-- | Transform GHC's CoreRule into an Equality.
ruleToEqualityT :: (BoundVars c, HasDynFlags m, HasHermitMEnv m, MonadThings m, MonadCatch m)
                => Transform c m CoreRule Equality
ruleToEqualityT = withPatFailMsg "HERMIT cannot handle built-in rules yet." $
  do r@Rule{} <- idR -- other possibility is "BuiltinRule"
     f <- lookupId $ ru_fn r
     return $ Equality (ru_bndrs r) (mkCoreApps (Var f) (ru_args r)) (ru_rhs r)

------------------------------------------------------------------------

-- | Run GHC's specConstr pass, and apply any rules generated.
specConstrR :: RewriteH ModGuts
specConstrR = prefixFailMsg "spec-constr failed: " $ do
    rs  <- extractT specRules
    e'  <- contextfreeT $ liftCoreM . SpecConstr.specConstrProgram
    rs' <- return e' >>> extractT specRules
    let specRs = deleteFirstsBy ((==) `on` ru_name) rs' rs
    guardMsg (notNull specRs) "no rules created."
    let applyAllR = extractR
                  $ repeatR
                  $ anyCallR
                  $ promoteExprR
                  $ rulesToRewrite specRs
    return e' >>> applyAllR

-- | Run GHC's specialisation pass, and apply any rules generated.
specialiseR :: RewriteH ModGuts
specialiseR = prefixFailMsg "specialisation failed: " $ do
    gRules <- arr mg_rules
    lRules <- extractT specRules

    guts <- contextfreeT $ liftCoreM . Specialise.specProgram

    lRules' <- return guts >>> extractT specRules -- spec rules on bindings in this module
    let gRules' = mg_rules guts            -- plus spec rules on imported bindings
        gSpecRs = deleteFirstsBy ((==) `on` ru_name) gRules' gRules
        lSpecRs = deleteFirstsBy ((==) `on` ru_name) lRules' lRules
        specRs = gSpecRs ++ lSpecRs
    guardMsg (notNull specRs) "no rules created."
    liftIO $ putStrLn $ unlines $ map (unpackFS . ru_name) specRs
    return guts >>> extractR (repeatR (anyCallR (promoteExprR $ rulesToRewrite specRs)))

-- | Get all the specialization rules on a binding.
--   These are created by SpecConstr and other GHC passes.
idSpecRules :: TransformH Id [CoreRule]
idSpecRules = do
    guardMsgM (arr isId) "idSpecRules called on TyVar." -- idInfo panics on TyVars
    contextfreeT $ \ i -> let SpecInfo rs _ = specInfo (idInfo i) in return rs

-- | Promote 'idSpecRules' to CoreBind.
bindSpecRules :: TransformH CoreBind [CoreRule]
bindSpecRules =    recT (\_ -> defT idSpecRules successT const) concat
                <+ nonRecT idSpecRules successT const

-- | Find all specialization rules in a Core fragment.
specRules :: TransformH Core [CoreRule]
specRules = crushtdT $ promoteBindT bindSpecRules

-- | Turn a list of rules into a rewrite which succeeds on the first successful rule.
-- Note: this should only be used for built-in and compiler-generated rules which we assume
-- are correct, because it does not record a lemma obligation for the rules used.
rulesToRewrite :: ( AddBindings c, ExtendPath c Crumb, HasEmptyContext c, ReadBindings c, ReadPath c Crumb
                  , HasDynFlags m, HasHermitMEnv m, MonadCatch m, MonadThings m, MonadUnique m )
               => [CoreRule] -> Rewrite c m CoreExpr
rulesToRewrite rs = catchesM [ (return r >>> ruleToEqualityT) >>= forwardT . birewrite | r <- rs ]

------------------------------------------------------------------------
