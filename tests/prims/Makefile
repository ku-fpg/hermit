test:: HERMIT.o
	perl ./test.pl BetaReduce
	perl ./test.pl BetaReduce h

	perl ./test.pl Fib
	perl ./test.pl Fib h

	perl ./test.pl Reverse
	perl ./test.pl Reverse h


.SUFFIXES: .o .hs
HERMIT.o: HERMIT.hs
	ghc-7.4.1 -c HERMIT.hs -fforce-recomp -O2 -dcore-lint -fsimple-list-literals


web::
	(cd ../../; make)
	perl ./test.pl Case w
