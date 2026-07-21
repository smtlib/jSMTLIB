mkfile_path := $(abspath $(lastword $(MAKEFILE_LIST)))
mkfile_dir  := $(dir $(mkfile_path))
TESTROOT    := $(patsubst %/,%,$(mkfile_dir))

## Sibling project roots
LSPROOT     := $(TESTROOT)/../../SMTlsp
SMTROOT     := $(TESTROOT)/../../SMT

SMTLIB_JAR  := $(SMTROOT)/jSMTLIB.jar
LSP_JAR     := $(LSPROOT)/build/smtlib-lsp.jar
LSP_SRCS    := $(shell find $(LSPROOT)/src -name '*.java')

## LSP4J + Gson (same versions as SMTlsp/Makefile)
LSP4J_VERSION := 1.0.0
LSPLIBS       := $(LSPROOT)/libs
LSP4J_CP      := $(LSPLIBS)/org.eclipse.lsp4j-$(LSP4J_VERSION).jar:$(LSPLIBS)/org.eclipse.lsp4j.jsonrpc-$(LSP4J_VERSION).jar:$(LSPLIBS)/gson-2.11.0.jar

## JUnit 4 (downloaded on first build)
LIBS          := $(TESTROOT)/libs
JUNIT_JAR     := $(LIBS)/junit-4.13.2.jar
HAMCREST_JAR  := $(LIBS)/hamcrest-core-1.3.jar
JUNIT_CP      := $(JUNIT_JAR):$(HAMCREST_JAR)

MAVEN := https://repo1.maven.org/maven2
JAVAC := javac
JAVA  := java

## Build output
CLASSES    := $(TESTROOT)/build/classes
RESULT_DIR := $(TESTROOT)/build/results

## Source trees: infrastructure in src/, test cases in test/
INFRA_SRCS := $(shell find $(TESTROOT)/src  -name '*.java')
TEST_SRCS  := $(shell find $(TESTROOT)/test -name '*.java')

## All test classes — each runs in its own JVM for isolation.
TEST_CLASSES := \
  InitializeTest \
  DiagnosticsTest \
  DocumentSymbolTest \
  WorkspaceSymbolTest \
  HoverTest \
  DocumentLifecycleTest \
  DebouncingTest

LOG_FILES := $(patsubst %,$(RESULT_DIR)/%.log,$(TEST_CLASSES))

.PHONY: all compile libs run-tests run-tests-seq _run-logs clean .FORCE

all: run-tests

## Download JUnit from Maven Central when not present
libs: $(JUNIT_JAR) $(HAMCREST_JAR)

$(JUNIT_JAR):
	@mkdir -p $(LIBS)
	curl --fail --show-error -s -o $@.tmp $(MAVEN)/junit/junit/4.13.2/junit-4.13.2.jar && mv $@.tmp $@ || (rm -f $@.tmp; false)

$(HAMCREST_JAR):
	@mkdir -p $(LIBS)
	curl --fail --show-error -s -o $@.tmp $(MAVEN)/org/hamcrest/hamcrest-core/1.3/hamcrest-core-1.3.jar && mv $@.tmp $@ || (rm -f $@.tmp; false)

## Build the LSP server jar when sources are newer than the jar
$(LSP_JAR): $(LSP_SRCS)
	$(MAKE) -C $(LSPROOT) jar

## Compile test infrastructure and test cases
compile: libs $(LSP_JAR)
	@mkdir -p $(CLASSES)
	$(JAVAC) \
	    -cp $(LSP_JAR):$(SMTLIB_JAR):$(LSP4J_CP):$(JUNIT_CP) \
	    -d $(CLASSES) \
	    $(INFRA_SRCS) $(TEST_SRCS)

## Sentinel used by per-class log targets
$(RESULT_DIR)/.compiled: compile
	@mkdir -p $(RESULT_DIR)
	@touch $@

## Per-class pattern rule — one JVM per test class
$(RESULT_DIR)/%.log: $(RESULT_DIR)/.compiled
	@echo "[TEST] $*"
	@_start=$$(date +%s); \
	if ( $(JAVA) \
	      -cp "$(CLASSES):$(LSP_JAR):$(SMTLIB_JAR):$(LSP4J_CP):$(JUNIT_CP)" \
	      org.junit.runner.JUnitCore \
	      org.smtlib.lsp.test.$* \
	  ) > $@ 2>&1; \
	then \
	  _elapsed=$$(( $$(date +%s) - _start )); \
	  grep -E "^OK|Tests run" $@ | tail -1 | sed "s/^/[PASS] $* ($${_elapsed}s): /"; \
	else \
	  _elapsed=$$(( $$(date +%s) - _start )); \
	  echo "[FAIL] $* ($${_elapsed}s) — log: $@"; \
	  cat $@; \
	  exit 1; \
	fi

## Run all test classes in parallel (default: 4 concurrent JVMs)
JOBS ?= 4

_run-logs: $(LOG_FILES)

run-tests: $(RESULT_DIR)/.compiled
	@$(MAKE) --no-print-directory -j$(JOBS) _run-logs
	@echo "All LSP tests passed."

## Sequential run — useful for debugging
run-tests-seq: $(RESULT_DIR)/.compiled
	@rm -f $(LOG_FILES)
	@$(MAKE) --no-print-directory -j1 _run-logs
	@echo "All LSP tests passed (sequential)."

## Run a single test: make test-DiagnosticsTest
test-%: .FORCE $(RESULT_DIR)/.compiled
	@$(MAKE) --no-print-directory -B $(RESULT_DIR)/$*.log

clean: .FORCE
	rm -rf $(TESTROOT)/build

.FORCE:
