HERMIT = perl ../../scripts/hermit.pl

test-fib:
	- $(HERMIT) Fib.hs resume
	./Fib

	- $(HERMIT) Fib.hs Fib.hss resume
	./Fib

rev:
	- $(HERMIT) Reverse.hs Reverse.hss resume

interactive-rev:
	- $(HERMIT) Reverse.hs

interactive-fib:
	$(HERMIT) Fib.hs

