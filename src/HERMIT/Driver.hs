module HERMIT.Driver where

ghcFlags :: [String]
ghcFlags = [ "-fforce-recomp"
           , "-O2"
           , "-dcore-lint"
           , "-fsimple-list-literals"
           , "-fexpose-all-unfoldings"
--           , "-v0"
           ]
