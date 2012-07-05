HERMIT = perl ../../scripts/hermit.pl
MODULE=Reverse

test-example:
	- $(HERMIT) $(MODULE).hs resume
	./$(MODULE)

	- $(HERMIT) $(MODULE).hs $(MODULE).hss resume
	./$(MODULE)

interactive-example:
	- $(HERMIT) Reverse.hs


