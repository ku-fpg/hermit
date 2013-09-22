install:
	( cd ../../../optimizations/streamfusion/hermit-streamfusion ; cabal install --force-reinstalls )

vector:
	ghc --make -O2 Concat.hs -fforce-recomp 

hvector:
	hermit Concat.hs -opt=HERMIT.Optimization.StreamFusion.Vector +Main 

time:
	time ./Concat
