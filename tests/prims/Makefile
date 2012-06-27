HERMIT = perl ../../scripts/runtests.pl

boot::
	- $(HERMIT) Test.hs Test.hss resume | tee Test.out
	diff -s Test.out Test.expected.out

interactive::
	- $(HERMIT) Test.hs
