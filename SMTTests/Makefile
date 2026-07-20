SHELL = /bin/bash

## Class files used for both the JaCoCo runtime agent and the report step.
## Must be the same in both places so that JaCoCo's CRC checks pass at report time.
## Default is the jar; override on the command line if you need .class files instead:
##   make cov-test cov-report COV_CLASSES=../SMT/bin
COV_CLASSES ?= ../SMT/jSMTLIB.jar

.PHONY: test clean script-tests smt-tests build local-setup cov-test cov-clean cov-report cov-show

tests: local-setup
	@result=0; \
	$(MAKE) script-tests || result=1; \
	$(MAKE) smt-tests || result=1; \
	exit $$result

## Generate jsmtlib.properties from $$SOLVERS when running outside CI.
## In CI the jsmtlib-test action writes this file directly before running make.
## Sources ./setup to pick up the SOLVERS default when the env var is not set.
local-setup:
	@if [ -z "$$CI" ]; then \
		source ./setup; \
		Z3_4_3=$$([ -f "$$SOLVERS/z3-4.3.1" ] && echo "$$SOLVERS/z3-4.3.1" || ([ -f "$$SOLVERS/z3-4.3.2" ] && echo "$$SOLVERS/z3-4.3.2" || echo "")); \
		Z3_4_8=$$([ -f "$$SOLVERS/z3-4.8.12" ] && echo "$$SOLVERS/z3-4.8.12" || echo ""); \
		CVC5=$$([ -f "$$SOLVERS/cvc5-1.6" ] && echo "$$SOLVERS/cvc5-1.6" || echo ""); \
		{ \
			echo "org.smtlib.logic_path="; \
			echo "org.smtlib.solver_z3.exec=$$Z3_4_3"; \
			echo "org.smtlib.solver_z3_4_3.exec=$$Z3_4_3"; \
			echo "org.smtlib.solver_z3_4_8.adapter=org.smtlib.solvers.Solver_z3_4_8"; \
			echo "org.smtlib.solver_z3_4_8.exec=$$Z3_4_8"; \
			echo "org.smtlib.solver_z3_4_8.command=$${Z3_4_8:+$$Z3_4_8,-smt2,-in,SMTLIB2_COMPLIANT=true}"; \
			echo "org.smtlib.solver_cvc5.exec=$$CVC5"; \
			echo "org.smtlib.solver_simplify.exec="; \
		} > jsmtlib.properties; \
		echo "Generated jsmtlib.properties from SOLVERS=$$SOLVERS"; \
	fi

script-tests:
	bash ./runscripts

smt-tests:
	bash ./runtests

clean:
	rm -f tempout scripts/tempout
	rm -f tests/*.actual tests/*.actual.tmp scripts/*.actual scripts/*.actual.tmp

build:
	$(MAKE) -C ../SMT build

## Run SMT tests with JaCoCo coverage instrumentation
cov-test: local-setup
	COV_CLASSES=$(COV_CLASSES) COV= bash ./runtests

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

