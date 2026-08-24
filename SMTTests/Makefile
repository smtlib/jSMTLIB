SHELL = /bin/bash

## Class files used for both the JaCoCo runtime agent and the report step.
## Must be the same in both places so that JaCoCo's CRC checks pass at report time.
## Default is the jar; override on the command line if you need .class files instead
## (note: ../SMT/buildRelease no longer populates ../SMT/bin -- it stages compiled
## classes in a temporary directory to avoid colliding with Eclipse's own incremental
## builder, which does still use ../SMT/bin as its output folder -- so this override
## only has classes to point at after an actual Eclipse build of the SMT project):
##   make cov-test cov-report COV_CLASSES=../SMT/bin
COV_CLASSES ?= ../SMT/jSMTLIB.jar

.PHONY: test tests test-only clean script-tests smt-tests junit-tests build cov-test cov-clean cov-report cov-show cov-all reports time-solvers

## Resolve the platform-appropriate solver directory, honouring any value already in the
## environment (CI sets it via GITHUB_ENV before invoking make; developers can export it
## manually to override the default).  setup computes the default from the platform/arch.
ifndef SMT_SOLVER_DIR
  SMT_SOLVER_DIR := $(shell . ./setup && echo "$$SMT_SOLVER_DIR")
endif
export SMT_SOLVER_DIR

## The solvers to test against (space-separated names, read by runjunits/runtests and by
## LogicTests.java/FileTests.java). Default is just the built-in pure-Java "test" solver,
## which needs no external binary. Override on the command line or in the environment, e.g.:
##   make test SMT_TEST_SOLVERS="test z3-4.3 z3_4_8 cvc5"
## yices2 (bare) rather than pinning both yices2-2.6.5/yices2-2.7.0: resolves to whichever
## version jsmtlib.properties designates default for the current platform, avoiding
## doubled test volume/golden upkeep for two versions when one representative suffices.
## Full z3 version lineup is now included -- 4.5.0/4.6.0/4.7.1/4.12.6 were previously
## dropped over inconsistent Solvers-repo availability on some platforms (missing on one
## or both ARM64 builds), but LogicTests.solversFromEnv() now filters any solver whose
## executable isn't present on the current platform out of the run up front (a WARNING,
## not a failure), so a version missing on some platform/arch no longer needs excluding
## from the whole list -- it's just silently skipped there and tested everywhere it exists.
## z3-5.1.0 has no jsmtlib.properties entry at all -- it relies entirely on the
## executable-name-equals-solvername convention plus SMT.startSolver's z3-prefix
## fallback to Solver_z3_recent, so it doubles as ongoing coverage for that fallback.
#SMT_TEST_SOLVERS ?=test z3-4.3 cvc5-1.3.2 z3-4.5.0 z3-4.6.0 z3-4.7.1 z3-4.8.12 z3-4.10.2 z3-4.12.6 z3-4.14.1 z3-4.16.0 z3-5.1.0 yices2 smtinterpol-2.5
## TEMPORARY: narrowed to just the new, not-yet-fully-CI-verified adapters (see
## Solver_bitwuzla.java/Solver_altergo.java and jsmtlib.properties) so CI results
## are easy to read while getting them working. Restore the line above (and delete
## this one) once all are confirmed working.
## altergo is deliberately EXCLUDED here, not just unverified: CI run 32671113041
## confirmed it hangs completely (never responds, not even to the first test) on
## every platform where the Solvers repo has a build (linux-x64, macos-arm64) --
## each burned the full 20-minute job timeout before being force-canceled. Its
## adapter was a documentation-only guess (no local binary was available) about
## reading a script from stdin; that assumption is now known wrong, or at least
## incomplete, and needs new evidence (ideally a local Linux/Docker repro) before
## trying again, not another blind CI iteration at ~20 minutes per guess.
## yices2 is included alongside bitwuzla/simplify (not just the bare "test" solver)
## so a real, already-verified solver runs in the same CI matrix -- this is what
## caught the Windows-only yices2 stderr-echo gap unmasked by the smtinterpol commit.
SMT_TEST_SOLVERS ?=test bitwuzla simplify yices2
export SMT_TEST_SOLVERS

test tests:
	$(MAKE) junit-tests

## Run all tests against only the built-in "test" solver (fast, needs no external
## solver binaries) -- overrides SMT_TEST_SOLVERS regardless of the environment/default.
test-only: SMT_TEST_SOLVERS := test
test-only: junit-tests

script-tests:
	bash ./runscripts

smt-tests:
	bash ./runtests

## Run the smt-tests suite against each solver in SMT_TEST_SOLVERS, one at a time,
## timing how long the full suite takes against each. Every line of output (each test as
## it runs), prefixed with elapsed seconds since that solver's run started, goes to a
## single log time-solvers-logs/time-solvers-<start-timestamp>.log (and matching summary
## file) -- timestamped so a second, concurrently-started run doesn't collide with or
## overwrite the first one's log. The terminal stays quiet during each solver's run
## (tail -f the log if you want to watch it live); only the "=== Timing <solver> ==="
## header and that solver's own concluding SUCCEEDED/FAILURES line are printed there, as
## soon as that solver finishes, and a summary (elapsed time + that line) is printed
## again in full at the end. Override the solver list the same way as SMT_TEST_SOLVERS,
## e.g.:
##   make time-solvers SMT_TEST_SOLVERS="z3-4.16.0 cvc5-1.3.2"
time-solvers:
	@mkdir -p time-solvers-logs
	@ts=$$(date +%Y%m%d-%H%M%S); \
	log=time-solvers-logs/time-solvers-$$ts.log; \
	summary=time-solvers-logs/summary-$$ts.txt; \
	: > "$$log"; \
	for solver in $(SMT_TEST_SOLVERS); do \
		echo "=== Timing $$solver ===" | tee -a "$$log"; \
		start=$$(date +%s); \
		bash ./runtests --solvers "$$solver" 2>&1 \
			| while IFS= read -r line; do printf '[%3ds] %s\n' "$$(($$(date +%s) - start))" "$$line"; done \
			>> "$$log"; \
		end=$$(date +%s); \
		elapsed=$$((end - start)); \
		result=$$(grep -E "SUCCEEDED|FAILURES" "$$log" | tail -1 | sed -E 's/^\[[ 0-9]+s\] //'); \
		echo "[$$elapsed] $$result"; \
		printf '%-20s %6ds   %s\n' "$$solver" "$$elapsed" "$$result" >> "$$summary"; \
	done; \
	echo; echo "=== time-solvers summary ($$log) ==="; cat "$$summary"

junit-tests:
	bash ./runjunits

clean:
	$(MAKE) -C ../SMT clean
	rm -f tempout scripts/tempout solver.out
	find tests scripts \( -name '*.actual' -o -name '*.actual.tmp' \) -delete
	rm -f bin/org/smtlib/test/UnitTests.class bin/org/smtlib/test/UnitTests\$$*.class
	rm -f reports/*.md
	rm -rf time-solvers-logs
	rm -rf junit-logs

## Regenerate the solver capability/options/logics reports (SMTTests/reports/*.md)
## by probing every discovered solver binary directly. Slow (the ALL-logic
## report alone runs ~750 probes across every z3/yices2 version found), so
## it's a separate target rather than part of the default test run.
reports:
	cd reports && python3 ALL-logic-report.py
	cd reports && python3 options-report.py
	cd reports && python3 logics-report.py

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
