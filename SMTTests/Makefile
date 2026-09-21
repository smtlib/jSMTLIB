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

.PHONY: test tests test-only clean script-tests smt-tests junit-tests build cov-test cov-clean cov-report cov-show cov-all reports time-solvers ci-cov ci-cov-dev

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
## bitwuzla and simplify were onboarded and CI-verified clean across all 5 platforms
## (goldens + adapter fixes) and are now part of the regular default list, same as
## every other solver here. altergo is deliberately EXCLUDED: CI run 32671113041
## confirmed it hangs completely (never responds, not even to the first test) on
## every platform where the Solvers repo has a build (linux-x64, macos-arm64) --
## each burned the full 20-minute job timeout before being force-canceled. Its
## adapter was a documentation-only guess (no local binary was available) about
## reading a script from stdin; that assumption is now known wrong, or at least
## incomplete, and needs new evidence (ideally a local Linux/Docker repro) before
## trying again, not another blind CI iteration at ~20 minutes per guess.
SMT_TEST_SOLVERS ?=test z3-4.3 cvc5-1.3.2 z3-4.5.0 z3-4.6.0 z3-4.7.1 z3-4.8.12 z3-4.10.2 z3-4.12.6 z3-4.14.1 z3-4.16.0 z3-5.1.0 yices2 smtinterpol-2.5 bitwuzla simplify
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

## Branch that ci-cov dispatches against; defaults to the repo's main branch. ci-cov-dev
## overrides this to 'dev' (for its own recipe and, per GNU Make's target-specific
## variable propagation, for ci-cov's recipe too when run as ci-cov-dev's prerequisite).
CI_BRANCH ?= master

## Override for the workflow_dispatch 'solvers' input (see .github/workflows/build.yml).
## Defaults to the same full solver list as SMT_TEST_SOLVERS above (spelled out here,
## rather than left blank, so the dispatched run and the "Dispatching..." echo both show
## explicitly what's being tested instead of relying on blank-means-default indirection).
CI_SOLVERS ?= $(SMT_TEST_SOLVERS)

## Launch a workflow_dispatch run of build.yml with coverage=true (see
## .github/actions/jsmtlib-test/action.yml), wait for it to finish, then download every
## per-leg coverage-<label> artifact it produces into cov/ci/. CI itself uploads one
## artifact per matrix leg (macos-arm64, macos-15-x86_64, ubuntu, ubuntu-arm64, windows),
## not a single merged one -- but each leg's raw cov/ci/coverage-<label>/junits.exec is
## then merged HERE, client-side, via jacococli's own merge command, into one
## cov/ci/merged.exec and a single consolidated cov/ci/html/coverage.xml report covering
## every platform's combined coverage -- since each platform exercises different
## solver-adapter code paths (isWindows/isMac branches, per-platform solver availability,
## etc.), a merged view is more useful than 5 separate reports to cross-reference by hand.
## Requires the gh CLI, authenticated against this repo (gh auth status).
## Override the dispatched branch or solver list on the command line, e.g.:
##   make ci-cov CI_BRANCH=dev CI_SOLVERS="test cvc5-1.3.2"
## (or just `make ci-cov-dev` -- see below).
## `gh workflow run` doesn't hand back a run id, and GitHub takes a few seconds to list a
## just-dispatched run -- the loop below polls `gh run list` every 5s, up to 12 times
## (~60s total), giving up if the run never shows up. NOTE: inline '#'-comments INSIDE
## this recipe's backslash-continued shell block are unsafe -- macOS's bundled GNU Make
## 3.81 strips them (backslash and all) before honouring line-continuation during real
## execution, silently truncating the whole chain (make -n does NOT reproduce this, so it
## looks fine under a dry run) -- keep recipe-body explanations up here instead.
ci-cov:
	@echo "Dispatching build.yml (coverage=true, solvers=\"$(CI_SOLVERS)\") on branch $(CI_BRANCH)..."
	@gh workflow run build.yml --ref $(CI_BRANCH) -f coverage=true -f solvers="$(CI_SOLVERS)"
	@sleep 5; \
	run_id=""; \
	for i in $$(seq 1 12); do \
		run_id=$$(gh run list --workflow build.yml --branch $(CI_BRANCH) --limit 10 --json databaseId,event --jq '[.[] | select(.event=="workflow_dispatch")][0].databaseId'); \
		[ -n "$$run_id" ] && break; \
		sleep 5; \
	done; \
	if [ -z "$$run_id" ]; then echo "ERROR: could not find the dispatched run"; exit 1; fi; \
	echo "Watching run $$run_id..."; \
	prev=""; \
	while :; do \
		info=$$(gh run view "$$run_id" --json status,conclusion,jobs); \
		rstatus=$$(echo "$$info" | jq -r '.status'); \
		line=$$(echo "$$info" | jq -r '.jobs[] | select(.name | startswith("test ")) | "  \(.name): \(if .status == "completed" then .conclusion else .status end)"'); \
		if [ "$$line" != "$$prev" ]; then echo "$$line"; prev="$$line"; fi; \
		[ "$$rstatus" = "completed" ] && break; \
		sleep 10; \
	done; \
	conclusion=$$(echo "$$info" | jq -r '.conclusion'); \
	echo "Run finished: $$conclusion"; \
	[ "$$conclusion" = "success" ] && status=0 || status=1; \
	echo "Downloading coverage artifacts to cov/ci/..."; \
	rm -rf cov/ci; mkdir -p cov/ci; \
	gh run download "$$run_id" -p 'coverage-*' -D cov/ci; \
	execs=$$(find cov/ci -name junits.exec); \
	if [ -z "$$execs" ]; then \
		echo "WARNING: no junits.exec files found in the downloaded artifacts -- skipping merge"; \
	else \
		echo "Merging $$(echo "$$execs" | wc -l | tr -d ' ') per-platform .exec files into one report..."; \
		java -jar jacoco/lib/jacococli.jar merge $$execs --destfile cov/ci/merged.exec; \
		java -jar jacoco/lib/jacococli.jar report cov/ci/merged.exec \
			--classfiles $(COV_CLASSES) \
			--sourcefiles ../SMT/src \
			--html cov/ci/html \
			--xml cov/ci/coverage.xml; \
		echo "Consolidated report: cov/ci/html/index.html"; \
	fi; \
	exit $$status

## Same as ci-cov, but against the dev branch instead of the main branch.
ci-cov-dev: CI_BRANCH := dev
ci-cov-dev: ci-cov
