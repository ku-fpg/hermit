install:
	( cd hermit-streamfusion ; cabal install --force-reinstalls )

list:
	ghc --make -O2 Main.hs -fforce-recomp -ddump-prep -ddump-to-file

hlist:
	hermit Main.hs -opt=HERMIT.Optimization.StreamFusion +Main -- -ddump-prep -ddump-to-file

vector:
	ghc --make -O2 Concat.hs -fforce-recomp -ddump-prep -ddump-simpl -ddump-to-file

hvector:
	hermit Concat.hs -opt=HERMIT.Optimization.StreamFusion.Vector +Main -- -ddump-prep -ddump-simpl -ddump-to-file
