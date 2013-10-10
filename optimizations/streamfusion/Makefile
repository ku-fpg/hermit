.PHONY : deep

install:
	( cd hermit-streamfusion ; cabal install --force-reinstalls )

deep:
	hermit Deep.hs -opt=HERMIT.Optimization.StreamFusion.Vector +Main Deep -- -ddump-simpl -ddump-to-file

list:
	ghc --make -O2 Main.hs -fforce-recomp -ddump-prep -ddump-to-file

hlist:
	hermit Main.hs -opt=HERMIT.Optimization.StreamFusion +Main -- -ddump-prep -ddump-to-file

vector:
	ghc --make -O2 Concat.hs -fforce-recomp -ddump-prep -ddump-simpl -ddump-to-file

hvector:
	hermit Concat.hs -opt=HERMIT.Optimization.StreamFusion.Vector +Main -- -ddump-prep -ddump-simpl -ddump-to-file -ddump-cmm -ddump-asm

int:
	ghc --make -O2 Intuition.hs -fforce-recomp -ddump-prep -ddump-to-file -Wall

hint:
	hermit Intuition.hs -opt=HERMIT.Optimization.StreamFusion +Main Intuition.hss -- -ddump-prep -ddump-simpl -ddump-to-file

paper:
	ghc --make -O2 PaperResults.hs -fforce-recomp -ddump-prep -ddump-to-file

hpaper:
	hermit PaperResults.hs -opt=HERMIT.Optimization.StreamFusion.Vector +Main -- -ddump-prep -ddump-simpl -ddump-to-file

