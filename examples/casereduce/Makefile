boot::
	(cd ../.. ; make boot )
	make comp

comp::
	ghc-7.4.1 -fplugin=Language.HERMIT.Plugin Main.hs \
		  -fplugin-opt=Language.HERMIT.Plugin:main:Main/CaseReduce.hermit  \
		  -fforce-recomp -dcore-lint
