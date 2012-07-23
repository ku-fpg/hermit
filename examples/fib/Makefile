HERMIT = perl ../../scripts/hermit.pl

fib:
	- $(HERMIT) Fib.hs Fib.hss resume

interactive:
	- $(HERMIT) Fib.hs Fib.hss

start:
	- $(HERMIT) Fib.hs

test:
	- rm *.o *.hi Fib
	- ghc --make -O2 -o Fib -fforce-recomp Fib.hs
	- ./Fib > timing.txt
	- echo "===========================================" >> timing.txt
	- $(HERMIT) Fib.hs Fib.hss resume
	- ./Fib >> timing.txt
	- cat timing.txt
