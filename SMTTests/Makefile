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
	@result=0; \
	$(MAKE) script-tests || result=1; \
	$(MAKE) smt-tests || result=1; \
	$(MAKE) junit-tests || result=1; \
	exit $$result

script-tests:
	bash ./runscripts

smt-tests:
	bash ./runtests

junit-tests:
	bash ./runjunits

clean:
	rm -f tempout scripts/tempout
	rm -f tests/*.actual tests/*.actual.tmp scripts/*.actual scripts/*.actual.tmp
	rm -f bin/org/smtlib/test/UnitTests.class bin/org/smtlib/test/UnitTests\$$*.class

build:
	$(MAKE) -C ../SMT build

## Run SMT tests and script tests with JaCoCo coverage instrumentation
cov-test:
	@result=0; \
	COV_CLASSES=$(COV_CLASSES) COV= bash ./runscripts; ret=$$?; [ $$ret -gt 128 ] && exit $$ret; [ $$ret -ne 0 ] && result=1; \
	COV_CLASSES=$(COV_CLASSES) COV= bash ./runtests;   ret=$$?; [ $$ret -gt 128 ] && exit $$ret; [ $$ret -ne 0 ] && result=1; \
	COV_CLASSES=$(COV_CLASSES) COV= bash ./runjunits;  ret=$$?; [ $$ret -gt 128 ] && exit $$ret; [ $$ret -ne 0 ] && result=1; \
	exit $$result

## Remove collected coverage data
cov-clean:
	rm -rf cov

## Merge .exec files and generate HTML + XML report
cov-report:
	java -jar jacoco/lib/jacococli.jar merge cov/*.exec --destfile cov/merged.exec
	java -jar jacoco/lib/jacococli.jar report cov/merged.exec \
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
