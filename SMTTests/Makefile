.PHONY: test clean script-tests smt-tests build

test:
	$(MAKE) script-tests
	$(MAKE) smt-tests

script-tests:
	./runscripts

smt-tests:
	./runtests

clean:
	rm -f tempout scripts/tempout
	rm -f tests/*.actual scripts/*.actual

build:
	$(MAKE) -C ../SMT build
	
