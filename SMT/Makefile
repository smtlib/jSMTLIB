.PHONY: build release test clean javadoc codeql

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

## CodeQL analysis with the security and code-quality queries, as the CodeQL workflow's manual
## security-and-quality run does (scope: ../.github/codeql/codeql-config.yml). Needs the CodeQL CLI:
## codeql on the PATH (e.g. brew install --cask codeql), or CODEQL=<path to codeql>. Writes
## temp/codeql/results.sarif and results.csv, and prints a count of alerts per query.
CODEQL = codeql

codeql:
	@command -v $(CODEQL) >/dev/null || { echo "CodeQL CLI not found; install it (brew install --cask codeql) or set CODEQL=<path>"; exit 1; }
	rm -rf temp/codeql/db
	mkdir -p temp/codeql
	$(CODEQL) database create temp/codeql/db --language=java --build-mode=none \
	    --source-root=.. --codescanning-config=../.github/codeql/codeql-config.yml
	$(CODEQL) database analyze temp/codeql/db --download --threads=0 \
	    codeql/java-queries:codeql-suites/java-security-and-quality.qls \
	    --format=sarif-latest --output=temp/codeql/results.sarif
	@# a second analysis reuses the stored query results
	$(CODEQL) database analyze temp/codeql/db --threads=0 \
	    codeql/java-queries:codeql-suites/java-security-and-quality.qls \
	    --format=csv --output=temp/codeql/results.csv
	@echo "Alerts per query (details in temp/codeql/results.csv):"
	@grep -o '"ruleId" *: *"[^"]*"' temp/codeql/results.sarif | sed 's/.*: *"\(.*\)"/\1/' | grep -v '/telemetry/\|/diagnostics/' | sort | uniq -c | sort -rn
