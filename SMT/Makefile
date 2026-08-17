.PHONY: build release test clean javadoc

build:
	./buildRelease

release:
	./buildRelease

## buildRelease holds .buildRelease.lock (a mkdir-based lock, see that script) for its
## whole run. Refuse to clean out from under it -- rm -rf temp/ mid-build would corrupt
## whatever buildRelease is currently compiling/assembling into that same directory.
clean:
	@if [ -d .buildRelease.lock ]; then \
		echo "ERROR: a ./buildRelease build is currently in progress (.buildRelease.lock exists) -- refusing to clean while it's running."; \
		exit 1; \
	fi
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
