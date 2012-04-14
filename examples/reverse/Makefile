boot::
#	(cd ../.. ; cabal clean ; cabal install )
	(cd ../.. ; make boot )
	make comp

comp::
	ghc-7.4.1 -fplugin=Language.HERMIT.Plugin Reverse.hs \
		  -fplugin-opt=Language.HERMIT.Plugin:main:Reverse/Reverse.hermit  \
		  -fforce-recomp -O2 -dcore-lint
