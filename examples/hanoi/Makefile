hanoi:
	- hermit Hanoi.hs Hanoi.hss resume

interactive:
	- hermit Hanoi.hs Hanoi.hss

test:
	- rm Hanoi *.o *.hi
	- ghc --make Hanoi.hs -O2 -o Hanoi
	- ./Hanoi
	- rm Hanoi *.o *.hi
	- hermit Hanoi.hs Hanoi.hss resume
	- ./Hanoi
