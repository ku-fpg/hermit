{-# LANGUAGE CPP #-}

module HERMIT.Plugin.Builder
    ( -- * The HERMIT Plugin
      HERMITPass
    , buildPlugin
    , CorePass(..)
    , getCorePass
    , ghcPasses
    , PassInfo(..)
    , getPassFlag
    )  where

import Data.IORef
import Data.List

import HERMIT.GHC
import HERMIT.Kernel

import System.IO

-- | Given a list of 'CommandLineOption's, produce the 'ModGuts' to 'ModGuts' function required to build a plugin.
type HERMITPass = IORef (Maybe (AST, ASTMap)) -> PassInfo -> [CommandLineOption] -> ModGuts -> CoreM ModGuts

-- | Build a plugin. This mainly handles the per-module options.
buildPlugin :: HERMITPass -> Plugin
buildPlugin hp = defaultPlugin { installCoreToDos = install }
    where
        install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
        install opts todos = do
            reinitializeGlobals

            -- This is a bit of a hack; otherwise we lose what we've not seen
            liftIO $ hSetBuffering stdout NoBuffering
#ifdef mingw32_HOST_OS
            -- This is a hacky workaround of a bug in Windows GHC.
            -- See https://ghc.haskell.org/trac/ghc/ticket/10301
            liftIO initStaticOpts
#endif

            store <- liftIO $ newIORef (Nothing :: Maybe (ModuleName, IORef (Maybe (AST, ASTMap))))
            let todos' = flattenTodos todos
                passes = map getCorePass todos'
                allPasses = foldr (\ (n,p,seen,notyet) r -> mkPass n seen notyet : p : r)
                                  [mkPass (length todos') passes []]
                                  (zip4 [0..] todos' (inits passes) (tails passes))
                mkPass n ps ps' = CoreDoPluginPass ("HERMIT" ++ show n)
                                $ modFilter store hp (PassInfo n ps ps') opts

            return allPasses

-- | Determine whether to act on this module, selecting global store.
-- NB: we have the ability to stick module info in the pass info here
modFilter :: IORef (Maybe (ModuleName, IORef (Maybe (AST, ASTMap)))) -- global store
          -> HERMITPass
          -> PassInfo
          -> [CommandLineOption]
          -> ModGuts -> CoreM ModGuts
modFilter store hp pInfo opts guts
    | null modOpts && notNull opts = return guts -- don't process this module
    | otherwise                    = do mb <- liftIO $ readIORef store
                                        modStore <- case mb of
                                                        Just (nm,ref) | nm == modName -> return ref
                                                        _ -> liftIO $ do
                                                            ref <- newIORef Nothing
                                                            writeIORef store $ Just (modName, ref)
                                                            return ref
                                        hp modStore pInfo (h_opts ++ filter notNull modOpts) guts
    where modOpts = filterOpts m_opts modName
          (m_opts, h_opts) = partition (isInfixOf ":") opts
          modName = moduleName $ mg_module guts

-- | Filter options to those pertaining to this module, stripping module prefix.
filterOpts :: [CommandLineOption] -> ModuleName -> [CommandLineOption]
filterOpts opts mname = [ opt | nm <- opts
                              , let mopt = if modName `isPrefixOf` nm
                                           then Just (drop len nm)
                                           else if "*:" `isPrefixOf` nm
                                                then Just (drop 2 nm)
                                                else Nothing
                              , Just opt <- [mopt]
                              ]
    where modName = moduleNameString mname
          len = lengthFS (moduleNameFS mname) + 1 -- for the colon

-- | An enumeration type for GHC's passes.
data CorePass = CallArity
              | CSE
              | Desugar
              | DesugarOpt
              | FloatInwards
              | FloatOutwards
              | LiberateCase
              | Prep
              | PrintCore
              | RuleCheck
              | Simplify
              | SpecConstr
              | Specialising
              | StaticArgs
              | Strictness
              | Tidy
              -- | Vectorisation
              | WorkerWrapper
              | Passes -- these should be flattened out in practice
              | PluginPass String
              | Exitify
              | OccurAnal
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
            -- , (Vectorisation, CoreDoVectorisation)
            , (Desugar      , CoreDesugar)    -- Right after desugaring, no simple optimisation yet!
            , (DesugarOpt   , CoreDesugarOpt) -- CoreDesugarXXX: Not strictly a core-to-core pass, but produces
            , (CallArity    , CoreDoCallArity)
            , (Tidy         , CoreTidy)
            , (Prep         , CorePrep)
            , (NoOp         , CoreDoNothing)
            , (OccurAnal    , CoreOccurAnal)
            , (Exitify      , CoreDoExitify)
            ]

getCorePass :: CoreToDo -> CorePass
getCorePass CoreDoFloatInwards       = FloatInwards
getCorePass CoreLiberateCase         = LiberateCase
getCorePass CoreDoPrintCore          = PrintCore
getCorePass CoreDoStaticArgs         = StaticArgs
getCorePass CoreDoStrictness         = Strictness
getCorePass CoreDoWorkerWrapper      = WorkerWrapper
getCorePass CoreDoSpecialising       = Specialising
getCorePass CoreDoSpecConstr         = SpecConstr
getCorePass CoreCSE                  = CSE
-- getCorePass CoreDoVectorisation      = Vectorisation
getCorePass CoreDesugar              = Desugar
getCorePass CoreDesugarOpt           = DesugarOpt
getCorePass CoreTidy                 = Tidy
getCorePass CorePrep                 = Prep
getCorePass (CoreDoSimplify {})      = Simplify
getCorePass (CoreDoFloatOutwards {}) = FloatOutwards
getCorePass (CoreDoRuleCheck {})     = RuleCheck
getCorePass (CoreDoPasses {})        = Passes -- these should be flattened out in practice
getCorePass (CoreDoPluginPass nm _)  = PluginPass nm
getCorePass CoreDoNothing            = NoOp
getCorePass CoreDoCallArity          = CallArity
getCorePass CoreDoExitify            = Exitify
getCorePass CoreOccurAnal            = OccurAnal

flattenTodos :: [CoreToDo] -> [CoreToDo]
flattenTodos = concatMap f
    where f (CoreDoPasses ps) = flattenTodos ps
          f CoreDoNothing     = []
          f other             = [other]

data PassInfo =
    PassInfo { passNum :: Int
             , passesDone :: [CorePass]
             , passesLeft :: [CorePass]
             }
    deriving (Read, Show, Eq)

-- | If HERMIT user specifies the -pN flag, get the N
-- TODO: as written will discard other flags that start with -p
getPassFlag :: [CommandLineOption] -> Maybe (Int, [CommandLineOption])
getPassFlag opts = case partition ("-p" `isPrefixOf`) opts of
                        ([],_) -> Nothing
                        (ps,r) -> Just (read (drop 2 (last ps)), r)
