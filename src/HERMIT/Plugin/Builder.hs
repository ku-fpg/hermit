{-# LANGUAGE CPP #-}

module HERMIT.Plugin.Builder
    ( -- * The HERMIT Plugin
      PluginPass
    , buildPlugin
    , CorePass(..)
    , getCorePass
    , ghcPasses
    , PhaseInfo(..)
    , getPhaseFlag
    )  where

import Data.List
import System.IO

import HERMIT.GHC

-- | Given a list of 'CommandLineOption's, produce the 'ModGuts' to 'ModGuts' function required to build a plugin.
type PluginPass = PhaseInfo -> [CommandLineOption] -> ModGuts -> CoreM ModGuts

-- | Build a plugin. This mainly handles the per-module options.
buildPlugin :: PluginPass -> Plugin
buildPlugin hp = defaultPlugin { installCoreToDos = install }
    where
        install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
        install opts todos = do
            reinitializeGlobals

            -- This is a bit of a hack; otherwise we lose what we've not seen
            liftIO $ hSetBuffering stdout NoBuffering
#ifdef mingw32_HOST_OS
            liftIO $ hSetEncoding stdout utf8
            liftIO resetStaticOpts
#endif

            let todos' = flattenTodos todos
                passes = map getCorePass todos'
                allPasses = foldr (\ (n,p,seen,notyet) r -> mkPass n seen notyet : p : r)
                                  [mkPass (length todos') passes []]
                                  (zip4 [0..] todos' (inits passes) (tails passes))
                mkPass n ps ps' = CoreDoPluginPass ("HERMIT" ++ show n) $ modFilter hp (PhaseInfo n ps ps') opts

            return allPasses

-- | Determine whether to act on this module, choose plugin pass.
-- NB: we have the ability to stick module info in the phase info here
modFilter :: PluginPass -> PluginPass
modFilter hp pInfo opts guts
    | null modOpts && notNull opts = return guts -- don't process this module
    | otherwise                    = hp pInfo (h_opts ++ filter notNull modOpts) guts
    where modOpts = filterOpts m_opts guts
          (m_opts, h_opts) = partition (isInfixOf ":") opts

-- | Filter options to those pertaining to this module, stripping module prefix.
filterOpts :: [CommandLineOption] -> ModGuts -> [CommandLineOption]
filterOpts opts guts = [ opt | nm <- opts
                             , let mopt = if modName `isPrefixOf` nm
                                          then Just (drop len nm)
                                          else if "*:" `isPrefixOf` nm
                                               then Just (drop 2 nm)
                                               else Nothing
                             , Just opt <- [mopt]
                             ]
    where modName = moduleNameString $ moduleName $ mg_module guts
          len = length modName + 1 -- for the colon

-- | An enumeration type for GHC's phases.
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

-- The following are not allowed yet because they required options.
-- CoreDoSimplify {- The core-to-core simplifier. -} Int {- Max iterations -} SimplifierMode
-- CoreDoFloatOutwards FloatOutSwitches
-- CoreDoRuleCheck CompilerPhase String   -- Check for non-application of rules matching this string
-- CoreDoPasses [CoreToDo]                -- lists of these things
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
-- getCorePass _                   = Unknown

flattenTodos :: [CoreToDo] -> [CoreToDo]
flattenTodos = concatMap f
    where f (CoreDoPasses ps) = flattenTodos ps
          f CoreDoNothing     = []
          f other             = [other]

data PhaseInfo =
    PhaseInfo { phaseNum :: Int
              , phasesDone :: [CorePass]
              , phasesLeft :: [CorePass]
              }
    deriving (Read, Show, Eq)

-- | If HERMIT user specifies the -pN flag, get the N
-- TODO: as written will discard other flags that start with -p
getPhaseFlag :: [CommandLineOption] -> Maybe (Int, [CommandLineOption])
getPhaseFlag opts = case partition ("-p" `isPrefixOf`) opts of
                        ([],_) -> Nothing
                        (ps,r) -> Just (read (drop 2 (last ps)), r)
