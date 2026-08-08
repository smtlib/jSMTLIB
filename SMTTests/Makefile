SHELL = /bin/bash

## Class files used for both the JaCoCo runtime agent and the report step.
## Must be the same in both places so that JaCoCo's CRC checks pass at report time.
## Default is the jar; override on the command line if you need .class files instead:
##   make cov-test cov-report COV_CLASSES=../SMT/bin
COV_CLASSES ?= ../SMT/jSMTLIB.jar

.PHONY: test tests clean script-tests smt-tests junit-tests build cov-test cov-clean cov-report cov-show

## Resolve the platform-appropriate solver directory, honouring any value already in the
## environment (CI sets it via GITHUB_ENV before invoking make; developers can export it
## manually to override the default).  setup computes the default from the platform/arch.
ifndef SMT_SOLVER_DIR
  SMT_SOLVER_DIR := $(shell . ./setup && echo "$$SMT_SOLVER_DIR")
endif
export SMT_SOLVER_DIR

test tests:
	$(MAKE) junit-tests

script-tests:
	bash ./runscripts

smt-tests:
	bash ./runtests --solvers "test z3_4_3"

junit-tests:
	bash ./runjunits

clean:
	rm -f tempout scripts/tempout
	rm -f tests/*.actual tests/*.actual.tmp scripts/*.actual scripts/*.actual.tmp
	rm -f bin/org/smtlib/test/UnitTests.class bin/org/smtlib/test/UnitTests\$$*.class

build:
	$(MAKE) -C ../SMT build

## Run all tests with JaCoCo coverage instrumentation.
## FileTests and the pure JUnit classes are instrumented via the agent on the
## main JVM; ScriptTests' spawned SMT processes are instrumented because
## runjunits sources setup-coverage before setup, so SMT_CMD carries the agent.
## All coverage is written to cov/junits.exec.
cov-test:
	COV_CLASSES=$(COV_CLASSES) COV= bash ./runjunits

## Remove collected coverage data
cov-clean:
	rm -rf cov

## Generate HTML + XML coverage report from the single exec file produced by cov-test
cov-report:
	java -jar jacoco/lib/jacococli.jar report cov/junits.exec \
		--classfiles $(COV_CLASSES) \
		--sourcefiles ../SMT/src \
		--html cov/html \
		--xml cov/coverage.xml

## Open the HTML coverage report in the default browser
cov-show:
	open cov/html/index.html

cov-all:
	-$(MAKE) cov-clean cov-test
	-$(MAKE) cov-report cov-show
