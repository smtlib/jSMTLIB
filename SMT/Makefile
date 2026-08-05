.PHONY: build release test clean javadoc

build:
	./buildRelease

release:
	./buildRelease

clean:
	rm -rf bin/ doc/ temp/
	rm -f jSMTLIB.jar jSMTLIB-sources.jar jSMTLIB.tar.gz
	rm -f src/org/smtlib/resources/version.properties

test:
	$(MAKE) -C ../SMTTests test

JAVADOC = $(if $(JAVA_HOME),$(JAVA_HOME)/bin/javadoc,javadoc)

javadoc:
	mkdir -p doc
	$(JAVADOC) -d doc \
	    -protected -author -version -use -splitindex \
	    -source 21 -sourcepath src \
	    -Xdoclint:all,-missing \
	    -doctitle "jSMTLIB API documentation" \
	    -subpackages org.smtlib \
	    src/APIExample.java
