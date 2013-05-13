module Language.HERMIT.Plugin
    ( -- * The HERMIT Plugin
      HermitPass
    , hermitPlugin
    , CorePass(..)
    , getCorePass
    , ghcPasses
    , PhaseInfo(..)
    )  where

import GhcPlugins
import Data.List
import System.IO

-- | Given a list of 'CommandLineOption's, produce the 'ModGuts' to 'ModGuts' function required to build a plugin.
type HermitPass = PhaseInfo -> [CommandLineOption] -> ModGuts -> CoreM ModGuts

-- | Build a hermit plugin. This mainly handles the per-module options.
hermitPlugin :: HermitPass -> Plugin
hermitPlugin hp = defaultPlugin { installCoreToDos = install }
    where
        install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
        install opts todos = do
            reinitializeGlobals

            -- This is a bit of a hack; otherwise we lose what we've not seen
            liftIO $ hSetBuffering stdout NoBuffering

            let (m_opts, _h_opts) = partition (isInfixOf ":") opts
                passes = map getCorePass todos
                allPasses = foldr (\ (n,p,seen,notyet) r -> mkPass n seen notyet : p : r)
                                  [mkPass (length todos) passes []]
                                  (zip4 [0..] todos (inits passes) (tails passes))
                mkPass n ps ps' = CoreDoPluginPass ("HERMIT" ++ show n) $ modFilter hp (PhaseInfo n ps ps') m_opts

            return allPasses

-- | Determine whether to act on this module, choose plugin pass.
-- NB: we have the ability to stick module info in the phase info here
modFilter :: HermitPass -> HermitPass
modFilter hp pi opts guts | null modOpts && not (null opts) = return guts -- don't process this module
                          | otherwise                       = hp pi (filter (not . null) modOpts) guts
    where modOpts = filterOpts opts guts

-- | Filter options to those pertaining to this module, stripping module prefix.
filterOpts :: [CommandLineOption] -> ModGuts -> [CommandLineOption]
filterOpts opts guts = [ drop len nm | nm <- opts, modName `isPrefixOf` nm ]
    where modName = moduleNameString $ moduleName $ mg_module guts
          len = length modName + 1 -- for the colon

data CorePass = FloatInwards
              | LiberateCase
              | PrintCore
              | StaticArgs
              | Strictness
              | WorkerWrapper
              | Specialising
              | SpecConstr
              | CSE
              | Vectorisation
              | Desugar
              | DesugarOpt
              | Tidy
              | Prep
              | Simplify
              | FloatOutwards
              | RuleCheck
              | Passes -- these should be flattened out in practice
              | PluginPass String
              | NoOp
              | Unknown
    deriving (Read, Show, Eq)

ghcPasses :: [(CorePass, CoreToDo)]
ghcPasses = [ (FloatInwards , CoreDoFloatInwards)
            , (LiberateCase , CoreLiberateCase)
            , (PrintCore    , CoreDoPrintCore)
            , (StaticArgs   , CoreDoStaticArgs)
            , (Strictness   , CoreDoStrictness)
            , (WorkerWrapper, CoreDoWorkerWrapper)
            , (Specialising , CoreDoSpecialising)
            , (SpecConstr   , CoreDoSpecConstr)
            , (CSE          , CoreCSE)
            , (Vectorisation, CoreDoVectorisation)
            , (Desugar      , CoreDesugar)    -- Right after desugaring, no simple optimisation yet!
            , (DesugarOpt   , CoreDesugarOpt) -- CoreDesugarXXX: Not strictly a core-to-core pass, but produces
            , (Tidy         , CoreTidy)
            , (Prep         , CorePrep)
            , (NoOp         , CoreDoNothing)
            ]

-- The following are not allowed yet because they required options.
-- CoreDoSimplify {- The core-to-core simplifier. -} Int {- Max iterations -} SimplifierMode
-- CoreDoFloatOutwards FloatOutSwitches
-- CoreDoRuleCheck CompilerPhase String   -- Check for non-application of rules matching this string
-- CoreDoPasses [CoreToDo]                -- lists of these things

getCorePass :: CoreToDo -> CorePass
getCorePass CoreDoFloatInwards  = FloatInwards
getCorePass CoreLiberateCase    = LiberateCase
getCorePass CoreDoPrintCore     = PrintCore
getCorePass CoreDoStaticArgs    = StaticArgs
getCorePass CoreDoStrictness    = Strictness
getCorePass CoreDoWorkerWrapper = WorkerWrapper
getCorePass CoreDoSpecialising  = Specialising
getCorePass CoreDoSpecConstr    = SpecConstr
getCorePass CoreCSE             = CSE
getCorePass CoreDoVectorisation = Vectorisation
getCorePass CoreDesugar         = Desugar
getCorePass CoreDesugarOpt      = DesugarOpt
getCorePass CoreTidy            = Tidy
getCorePass CorePrep            = Prep
getCorePass (CoreDoSimplify {}) = Simplify
getCorePass (CoreDoFloatOutwards {}) = FloatOutwards
getCorePass (CoreDoRuleCheck {}) = RuleCheck
getCorePass (CoreDoPasses {})   = Passes -- these should be flattened out in practice
getCorePass (CoreDoPluginPass nm _) = PluginPass nm
getCorePass CoreDoNothing       = NoOp
getCorePass _                   = Unknown

data PhaseInfo = 
    PhaseInfo { phaseNum :: Int
              , phasesDone :: [CorePass]
              , phasesLeft :: [CorePass]
              }
    deriving (Read, Show, Eq)
