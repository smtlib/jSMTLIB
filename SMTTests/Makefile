SHELL = /bin/bash

.PHONY: test clean script-tests smt-tests build local-setup

test: local-setup
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
		Z3_4_3=$$([ -f "$$SOLVERS/z3-4.3.1" ] && echo "$$SOLVERS/z3-4.3.1" || echo ""); \
		Z3_4_8=$$([ -f "$$SOLVERS/z3-4.8.12" ] && echo "$$SOLVERS/z3-4.8.12" || echo ""); \
		CVC4=$$([ -f "$$SOLVERS/cvc4-1.6" ] && echo "$$SOLVERS/cvc4-1.6" || echo ""); \
		{ \
			echo "org.smtlib.solver_z3.exec=$$Z3_4_3"; \
			echo "org.smtlib.solver_z3_4_3.exec=$$Z3_4_3"; \
			echo "org.smtlib.solver_z3_4_8.adapter=org.smtlib.solvers.Solver_z3_4_8"; \
			echo "org.smtlib.solver_z3_4_8.exec=$$Z3_4_8"; \
			if [ -n "$$Z3_4_8" ]; then echo "org.smtlib.solver_z3_4_8.command=$$Z3_4_8,-smt2,-in,SMTLIB2_COMPLIANT=true"; \
			else echo "org.smtlib.solver_z3_4_8.command="; fi; \
			echo "org.smtlib.solver_cvc4.exec=$$CVC4"; \
			echo "org.smtlib.solver_simplify.exec="; \
		} > jsmtlib.properties; \
		echo "Generated jsmtlib.properties from SOLVERS=$$SOLVERS"; \
	fi

script-tests:
	./runscripts

smt-tests:
	./runtests

clean:
	rm -f tempout scripts/tempout
	rm -f tests/*.actual scripts/*.actual

build:
	$(MAKE) -C ../SMT build
	
