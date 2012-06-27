HERMIT = perl ../../scripts/hermit.pl

test-fib:
	- $(HERMIT) Fib.hs resume
	./Fib

	- $(HERMIT) Fib.hs Fib.hss resume
	./Fib

interactive-fib:
	$(HERMIT) Fib.hs

