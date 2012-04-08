boot::
#	(cd ../.. ; cabal clean ; cabal install )
	(cd ../.. ; cabal install )
	make comp

comp::
	ghc-7.4.1 -fplugin=Language.HERMIT.Plugin Main.hs -fplugin-opt=Language.HERMIT.Plugin:cl -fforce-recomp -O2