        {-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module HERMIT.Dictionary.Rules
    ( -- * GHC Rewrite Rules and Specialisation
      externals
      -- ** Rules
    , RuleName(..)
    , RuleNameListBox(..)
    , foldRuleR
    , foldRulesR
    , unfoldRuleR
    , unfoldRulesR
    , compileRulesT
    , ruleToClauseT
    , ruleNameToClauseT
    , getHermitRuleT
    , getHermitRulesT
    , rulesHelpListT
    , ruleHelpT
    , lemmaHelpT
    , ruleToLemmaT
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
import HERMIT.External
import HERMIT.GHC
import HERMIT.Kure
import HERMIT.Lemma
import HERMIT.Monad

import HERMIT.Dictionary.Fold (compileFold, CompiledFold, toEqualities)
import HERMIT.Dictionary.Kure (anyCallR)
import HERMIT.Dictionary.Reasoning hiding (externals)

import HERMIT.PrettyPrinter.Common
import HERMIT.PrettyPrinter.Glyphs

import IOEnv hiding (liftIO)

------------------------------------------------------------------------

-- | Externals dealing with GHC rewrite rules.
externals :: [External]
externals =
    [ external "show-rules" (rulesHelpListT :: TransformH LCoreTC String)
        [ "List all the rules in scope." ] .+ Query
    , external "show-rule" (ruleHelpT :: PrettyPrinter -> RuleName -> TransformH LCoreTC Glyphs)
        [ "Display details on the named rule." ] .+ Query
    , external "fold-rule" (promoteExprR . foldRuleR Obligation :: RuleName -> RewriteH LCore)
        [ "Apply a named GHC rule right-to-left." ] .+ Shallow
    , external "fold-rules" (promoteExprR . foldRulesR Obligation :: [RuleName] -> RewriteH LCore)
        [ "Apply named GHC rules right-to-left, succeed if any of the rules succeed." ] .+ Shallow
    , external "unfold-rule" (promoteExprR . unfoldRuleR Obligation :: RuleName -> RewriteH LCore)
        [ "Apply a named GHC rule left-to-right." ] .+ Shallow
    , external "unfold-rule-unsafe" (promoteExprR . unfoldRuleR UnsafeUsed :: RuleName -> RewriteH LCore)
        [ "Apply a named GHC rule left-to-right." ] .+ Shallow .+ Unsafe
    , external "unfold-rules" (promoteExprR . unfoldRulesR Obligation :: [RuleName] -> RewriteH LCore)
        [ "Apply named GHC rules left-to-right, succeed if any of the rules succeed" ] .+ Shallow
    , external "unfold-rules-unsafe" (promoteExprR . unfoldRulesR UnsafeUsed :: [RuleName] -> RewriteH LCore)
        [ "Apply named GHC rules left-to-right, succeed if any of the rules succeed" ] .+ Shallow .+ Unsafe
    , external "rule-to-lemma" (lemmaHelpT :: PrettyPrinter -> RuleName -> TransformH LCore Glyphs)
        [ "Create a lemma from a GHC RULE." ]
    , external "spec-constr" (promoteModGutsR specConstrR :: RewriteH LCore)
        [ "Run GHC's SpecConstr pass, which performs call pattern specialization."] .+ Deep
    , external "specialise" (promoteModGutsR specialiseR :: RewriteH LCore)
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

-- | Lookup a rule by name, attempt to apply it left-to-right. If successful, record it as an unproven lemma.
foldRuleR :: ( AddBindings c, ExtendPath c Crumb, HasCoreRules c, HasEmptyContext c, LemmaContext c, ReadBindings c
             , ReadPath c Crumb, HasDynFlags m, HasHermitMEnv m, HasLemmas m, LiftCoreM m, MonadCatch m
             , MonadIO m, MonadThings m, MonadUnique m )
            => Used -> RuleName -> Rewrite c m CoreExpr
foldRuleR u nm = do
    q <- ruleNameToClauseT nm
    backwardT (birewrite q) >>> (verifyOrCreateT u (fromString (show nm)) q >> idR)

-- | Lookup a set of rules by name, attempt to apply them left-to-right. Record an unproven lemma for the one that succeeds.
foldRulesR :: ( AddBindings c, ExtendPath c Crumb, HasCoreRules c, HasEmptyContext c, LemmaContext c, ReadBindings c
              , ReadPath c Crumb, HasDynFlags m, HasHermitMEnv m, HasLemmas m, LiftCoreM m, MonadCatch m
              , MonadIO m, MonadThings m, MonadUnique m )
           => Used -> [RuleName] -> Rewrite c m CoreExpr
foldRulesR u = orR . map (foldRuleR u)

-- | Lookup a rule by name, attempt to apply it left-to-right. If successful, record it as an unproven lemma.
unfoldRuleR :: ( AddBindings c, ExtendPath c Crumb, HasCoreRules c, HasEmptyContext c, LemmaContext c, ReadBindings c
               , ReadPath c Crumb, HasDynFlags m, HasHermitMEnv m, HasLemmas m, LiftCoreM m, MonadCatch m
               , MonadIO m, MonadThings m, MonadUnique m )
            => Used -> RuleName -> Rewrite c m CoreExpr
unfoldRuleR u nm = do
    q <- ruleNameToClauseT nm
    forwardT (birewrite q) >>> (verifyOrCreateT u (fromString (show nm)) q >> idR)

-- | Lookup a set of rules by name, attempt to apply them left-to-right. Record an unproven lemma for the one that succeeds.
unfoldRulesR :: ( AddBindings c, ExtendPath c Crumb, HasCoreRules c, HasEmptyContext c, LemmaContext c, ReadBindings c
                , ReadPath c Crumb, HasDynFlags m, HasHermitMEnv m, HasLemmas m, LiftCoreM m, MonadCatch m
                , MonadIO m, MonadThings m, MonadUnique m )
             => Used -> [RuleName] -> Rewrite c m CoreExpr
unfoldRulesR u = orR . map (unfoldRuleR u)

-- | Can be used with runFoldR. Note: currently doesn't create a lemma for the rule used.
compileRulesT :: (BoundVars c, HasCoreRules c, HasHermitMEnv m, LiftCoreM m, MonadCatch m, MonadIO m, MonadThings m)
              => [RuleName] -> Transform c m a CompiledFold
compileRulesT nms = do
    let suggestion = "If you think the rule exists, try running the flatten-module command at the top level."
    let failMsg []   = "no rule names supplied."
        failMsg [nm] = "failed to find rule: " ++ show nm ++ ". " ++ suggestion
        failMsg _    = "failed to find any rules named " ++ intercalate ", " (map show nms) ++ ". " ++ suggestion
    allRules <- getHermitRulesT
    case filter ((`elem` nms) . fst) allRules of
        [] -> fail (failMsg nms)
        rs -> liftM (compileFold . concatMap toEqualities)
                $ forM (map snd rs) $ \ r -> return r >>> ruleToClauseT


-- | Return all in-scope CoreRules (including specialization RULES on binders), with their names.
getHermitRulesT :: (HasCoreRules c, HasHermitMEnv m, LiftCoreM m, MonadIO m) => Transform c m a [(RuleName, CoreRule)]
getHermitRulesT = contextonlyT $ \ c -> do
    rb      <- liftCoreM getRuleBase
    mgRules <- liftM mg_rules getModGuts
    hscEnv  <- getHscEnv
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

-- | Print a named CoreRule using the quantified printer.
ruleHelpT :: (HasCoreRules c, LemmaContext c, ReadBindings c, ReadPath c Crumb)
          => PrettyPrinter -> RuleName -> Transform c HermitM a Glyphs
ruleHelpT pp nm =
  do doc <- ruleNameToClauseT nm >>> liftPrettyH (pOptions pp) (extractT $ pLCoreTC pp)
     return $! renderCode (pOptions pp) doc

lemmaHelpT :: PrettyPrinter -> RuleName -> TransformH LCore Glyphs
lemmaHelpT pp nm =
  do doc <- ruleToLemmaT nm >> liftPrettyH (pOptions pp) (showLemmaT (fromString (show nm)) pp)
     return $! renderCode (pOptions pp) doc

-- | Build an Clause from a named GHC rewrite rule.
ruleNameToClauseT :: ( BoundVars c, HasCoreRules c, HasDynFlags m, HasHermitMEnv m
                       , LiftCoreM m, MonadCatch m, MonadIO m, MonadThings m )
                  => RuleName -> Transform c m a Clause
ruleNameToClauseT name = getHermitRuleT name >>> ruleToClauseT

-- | Transform GHC's CoreRule into an Clause.
ruleToClauseT :: (BoundVars c, HasHermitMEnv m, MonadThings m, MonadCatch m)
              => Transform c m CoreRule Clause
ruleToClauseT = withPatFailMsg "HERMIT cannot handle built-in rules yet." $ do
    r@Rule{} <- idR -- other possibility is "BuiltinRule"
    f <- lookupId $ ru_fn r
    let lhs = mkCoreApps (varToCoreExpr f) (ru_args r)
    return $ mkClause (ru_bndrs r) lhs (ru_rhs r)

ruleToLemmaT :: ( BoundVars c, HasCoreRules c, HasDynFlags m, HasHermitMEnv m, HasLemmas m
                , LiftCoreM m, MonadCatch m, MonadIO m, MonadThings m)
             => RuleName -> Transform c m a ()
ruleToLemmaT nm = do
    q <- ruleNameToClauseT nm
    insertLemmaT (fromString (show nm)) $ Lemma q NotProven NotUsed

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
rulesToRewrite rs = catchesM [ (return r >>> ruleToClauseT) >>= forwardT . birewrite | r <- rs ]

------------------------------------------------------------------------
