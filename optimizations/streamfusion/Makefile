build:
	( cd hermit-streamfusion ; cabal install --force-reinstalls )

run:
	hermit Main.hs -opt=HERMIT.Optimization.StreamFusion +Main -- -ddump-simpl -ddump-to-file

flatten:
	ghc --make -O2 Concat.hs -fforce-recomp -ddump-prep -ddump-to-file
