.PHONY: build release test clean javadoc

build:
	./buildRelease

release:
	./buildRelease
	cp jSMTLIB.jar jSMTLIB-$(shell cat version.txt).jar
	@echo "Release JAR: jSMTLIB-$(shell cat version.txt).jar"

clean:
	rm -rf bin/ doc/ temp/
	rm -f jSMTLIB.jar jSMTLIB.tar.gz jSMTLIB-*.jar
	rm -f src/org/smtlib/resources/version.properties

test:
	$(MAKE) -C ../SMTTests test

javadoc:
	ant -f javadoc.xml
