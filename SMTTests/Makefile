.PHONY: test clean script-tests smt-tests build

test:
	@result=0; \
	$(MAKE) script-tests || result=1; \
	$(MAKE) smt-tests || result=1; \
	exit $$result

script-tests:
	./runscripts

smt-tests:
	./runtests

clean:
	rm -f tempout scripts/tempout
	rm -f tests/*.actual scripts/*.actual

build:
	$(MAKE) -C ../SMT build
	
