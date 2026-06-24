.PHONY: build test clean

build:
	./buildRelease

clean:
	rm -rf bin/ doc/ temp/
	rm -f jSMTLIB.jar jSMTLIB.tar.gz
	rm -f solver.out tempout
	rm -f src/org/smtlib/resources/version.properties

test:
	$(MAKE) -C ../SMTTests test
