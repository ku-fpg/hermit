module HERMIT.Driver where

import Data.Version
import Paths_hermit as P

hermit_version :: String   
hermit_version = "HERMIT v" ++ showVersion P.version

ghcFlags :: [String]
ghcFlags = [ "-fforce-recomp"
           , "-O2"
           , "-dcore-lint"
           , "-fsimple-list-literals"
           , "-fexpose-all-unfoldings"
--           , "-v0"
           ]
