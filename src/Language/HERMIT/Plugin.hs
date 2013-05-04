module Language.HERMIT.Plugin
       ( -- * The HERMIT Plugin
         HermitPass
       , hermitPlugin
)  where

import GhcPlugins
import Data.List
import System.IO

import Data.Char (isDigit)
import Data.Default

-- | Given a list of 'CommandLineOption's, produce the 'ModGuts' to 'ModGuts' function required to build a plugin.
type HermitPass = [CommandLineOption] -> ModGuts -> CoreM ModGuts

data Options = Options { pass :: Int }

instance Default Options where
    def = Options { pass = 0 }

parse :: [String] -> Options -> Options
parse (('-':'p':n):rest) o | all isDigit n = parse rest $ o { pass = read n }
parse (_:rest) o = parse rest o -- unknown option
parse [] o       = o

-- | Build a hermit plugin. This mainly handles the per-module options.
hermitPlugin :: HermitPass -> Plugin
hermitPlugin hp = defaultPlugin { installCoreToDos = install }
    where
        install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
        install opts todos = do
            reinitializeGlobals

            -- This is a bit of a hack; otherwise we lose what we've not seen
            liftIO $ hSetBuffering stdout NoBuffering

            let (m_opts, h_opts) = partition (isInfixOf ":") opts
                hermit_opts = parse h_opts def
                myPass = CoreDoPluginPass "HERMIT" $ modFilter hp m_opts
                -- at front, for now
                allPasses = insertAt (pass hermit_opts) myPass todos

            return allPasses

-- | Determine whether to act on this module, choose plugin pass.
modFilter :: HermitPass -> HermitPass
modFilter hp opts guts | null modOpts && not (null opts) = return guts -- don't process this module
                       | otherwise                       = hp (filter (not . null) modOpts) guts
    where modOpts = filterOpts opts guts

-- | Filter options to those pertaining to this module, stripping module prefix.
filterOpts :: [CommandLineOption] -> ModGuts -> [CommandLineOption]
filterOpts opts guts = [ drop len nm | nm <- opts, modName `isPrefixOf` nm ]
    where modName = moduleNameString $ moduleName $ mg_module guts
          len = length modName + 1 -- for the colon

insertAt :: Int -> a -> [a] -> [a]
insertAt n x xs = pre ++ (x : suf)
    where (pre,suf) = splitAt n xs
